/- Repeated marks: fork of Collet's final-stage module Geometry (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the PR69 `Parameters` at theta = 174799/200000, h = 8053/10000 -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Submissions.density_split_third_20261026.Return.Constants
set_option autoImplicit false
namespace QRH.DensitySplitThird.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalParameters : Parameters where
  theta := QRH.DensitySplitThird.Return.theta
  ell := QRH.DensitySplitThird.Return.ell
  x := QRH.DensitySplitThird.Return.x
  y := QRH.DensitySplitThird.Return.y
  ell_pos := by norm_num [QRH.DensitySplitThird.Return.ell,QRH.DensitySplitThird.Return.c]
  sixth_lt_ell := by norm_num [QRH.DensitySplitThird.Return.ell,QRH.DensitySplitThird.Return.c]
  ell_lt_fifth := by norm_num [QRH.DensitySplitThird.Return.ell,QRH.DensitySplitThird.Return.c]
  ell_lt_x := by norm_num [QRH.DensitySplitThird.Return.x,QRH.DensitySplitThird.Return.ell,QRH.DensitySplitThird.Return.c,QRH.DensitySplitThird.Return.h]
  x_lt_y := by norm_num [QRH.DensitySplitThird.Return.x,QRH.DensitySplitThird.Return.y,QRH.DensitySplitThird.Return.ell,QRH.DensitySplitThird.Return.c,QRH.DensitySplitThird.Return.h]
  y_lt_half := by norm_num [QRH.DensitySplitThird.Return.y,QRH.DensitySplitThird.Return.ell,QRH.DensitySplitThird.Return.c,QRH.DensitySplitThird.Return.h]
  x_add_y := by dsimp [QRH.DensitySplitThird.Return.x,QRH.DensitySplitThird.Return.y];ring
  dilation_gap := by norm_num [QRH.DensitySplitThird.Return.x,QRH.DensitySplitThird.Return.y,QRH.DensitySplitThird.Return.ell,QRH.DensitySplitThird.Return.c,QRH.DensitySplitThird.Return.h]
  tuple_margin_neg := by norm_num [QRH.DensitySplitThird.Return.x,QRH.DensitySplitThird.Return.y,QRH.DensitySplitThird.Return.ell,QRH.DensitySplitThird.Return.c,QRH.DensitySplitThird.Return.h]
  signal_boundary := QRH.DensitySplitThird.Return.geometry_mellin
end QRH.DensitySplitThird.Return.Geometry
