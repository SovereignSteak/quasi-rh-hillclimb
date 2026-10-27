"""Check local Lean snapshots against pinned upstream Git blob IDs."""
from pathlib import Path
import hashlib,json

ROOT=Path(__file__).resolve().parent
HEAD='71996e7e79840455f7beead063a73b7b31cfb586'
BASE='submissions/density-split-third-20261026/src/Submissions/density_split_third_20261026/'
PINS={
 'HybridGates.lean':('Source/HybridGates.lean','1882d37869cd241ad0ea51678205a441686cd62c'),
 'HybridCertificatesThird.lean':('Source/HybridCertificatesThird.lean','f5a07ebc4060348d0c9bff3f080d1a982af60030'),
 'Assembly.lean':('Source/Assembly.lean','f86d673c7056c8b136f5747e7ccaf85fa61ac6e5'),
 'NativeBootstrap.lean':('Source/NativeBootstrap.lean','8329bdc165864e76808af94e451a15a89954f2a8'),
 'Price.lean':('Density/Price.lean','cb5f4c54b01661317754babaf77a678e570c2ebe'),
 'StepGates.lean':('Density/StepGates.lean','cb7bf1f4f22a7302c0ab190737c8ea29471c601c'),
 'Leaf.lean':('Density/Leaf.lean','8aa92a1fc50cb4b1f4e4341d507c4e189780304f'),
 'ReturnConstants.lean':('Return/Constants.lean','128d19fc9c7620bc9ce014757c309f73789419a4'),
 'CountWindow.lean':('Return/CountWindow.lean','1cae659efd4165658cd2c55c0a55493b6e7b9a11'),
 'ReturnFinalSchedule.lean':('Return/FinalSchedule.lean','e53504a0c669e0b769f69b22d6ebf87a1cd3ed50'),
 'GenericScalar.lean':('ReturnD/GenericScalar.lean','b6386ad9a5bd9aa11f95a4cdab2567fc9de3a922'),
 'ReturnFormulas.lean':('Return/Formulas.lean','bb35e970957296fbb0d98e585b108ae63e091bb6'),
 'CountAdmission.lean':('Return/CountAdmission.lean','7ac0964b54365eb135a440e88e07c0f8016671e4'),
 'CountWidth.lean':('Return/CountWidth.lean','d4545c0ac09b3175ac926c69ae674d3bd8c85a45'),
 'CountDecode.lean':('Return/CountDecode.lean','56e3fe93f288ca995ed3e5f247a43053d92f2d0c'),
 'Windows.lean':('Return/Windows.lean','c12a54e4bed6d6ea197741f046efc2bddb92baa3'),
 'Endpoint.lean':('Endpoint.lean','f92d2805f66f9345d9fc5fb0771484d51740ac20'),
 'Theorem.lean':('Theorem.lean','7bffe8d67abf0bb16eeaef572183d3b6d005592f'),
 'CubeFreeClosed.lean':('CubeFree/Assembly/Closed.lean','a639e7230f59b0aaf47e1f9b94d2e6ce7cafe656'),
 'CubeFreeFinal.lean':('CubeFree/Assembly/Final.lean','a59ef9fe7f1095f7ea6743ede9b5c144fe6c1c06'),
 'CubeFreeProvider.lean':('CubeFree/Assembly/Provider.lean','1bd2f7a4c7852198c269889473183d8ba9d77651'),
 'CubeFreeStep.lean':('CubeFree/Step.lean','d0903a200e81df75476abffabd6daa0195cbd213'),
 'CubeFreeLeaves.lean':('CubeFree/Assembly/Leaves.lean','7eae530ce2769a8be2a32b0f2afded34bc2dc17b'),
 'Schedule.lean':('ReturnD/Schedule.lean','3041e8ec38f3037c1ea972656ae6b633c6eb7cf8'),
 'FinalScheme.lean':('Return/FinalScheme.lean','5d722b379958dcb8ac1df6ec519aea0063c9ed04'),
 'Geometry.lean':('Return/Geometry.lean','908ed2fab95d32cb859f4a8bfa1bce64b8623f54'),
 'TransportInstances.lean':('Return/TransportInstances.lean','b71326439ac088b2334b9ad81e5a6797f9b33099'),
 'TransportGeometry.lean':('ReturnD/TransportGeometry.lean','cb39603756cfe5f77709e43bdc2f1f745b0a7fc8'),
 'FinalRows.lean':('Return/FinalRows.lean','5b9f44c7a4e0714d2845484ec97bce71a7d76bb3'),
 'Conductor.lean':('Return/Conductor.lean','0b2fca52f720087e61e5bf526ec5258a909a6efa'),
 'EndpointFromSources.lean':('Return/EndpointFromSources.lean','06299200d9381695c7639d87df69f5c8374780b4'),
 'WindowSources.lean':('Return/WindowSources.lean','1f0db16567889cbf1140e04e2565ab59f2fda133'),
 'BaseGeometry.lean':('../hailey_collet_1252270103/Record1252270103Return/Geometry.lean','3a988832ab04c920a2fe23bb784f9a3f76f77348'),
}

def git_hash(data):return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def main(normalize=False):
    rows=[]
    for name,(path,expected) in PINS.items():
      file=ROOT/name;data=file.read_bytes()
      if normalize:
        # gh --jq base64d and apply_patch can append output newlines. Only
        # normalize if the result matches the upstream Git content hash.
        for n in range(4):
          candidate=data[:-n] if n else data
          if git_hash(candidate)==expected:
            if n:file.write_bytes(candidate)
            data=candidate;break
      if git_hash(data)!=expected:raise ValueError((name,git_hash(data),expected))
      upstream=BASE+path if name!='BaseGeometry.lean' else 'submissions/hailey-collet-1252270103/src/Submissions/hailey_collet_1252270103/Record1252270103Return/Geometry.lean'
      rows.append(dict(local=name,upstream=upstream,git_blob=expected,sha256=hashlib.sha256(data).hexdigest(),
        url=f'https://github.com/GTimG/QuasiRiemannTracker/blob/{HEAD}/{upstream}'))
    (ROOT/'source-pins.json').write_text(json.dumps(dict(repository='GTimG/QuasiRiemannTracker',head=HEAD,sources=rows),indent=2)+'\n')
    print('Pinned source snapshots:',len(rows),'Git blobs verified')

if __name__=='__main__':
    import sys
    main('--normalize' in sys.argv[1:])
