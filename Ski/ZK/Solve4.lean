import Ski.ZK.MaskOOD
import Ski.ZK.Chain

/-!
# Four coefficients over `F` reach any point of the extension

A polynomial over `F` with four coefficients takes any value `e` of the
extension at `z` when `1, z, z², z³` are independent over `F`: the
coefficients solve `M a = e`, `M` the powers' coordinates (`mz z`), by the
adjugate (`M4.solve`, `solve_spec`).  The adjugate's identities
`M · adj M = det M · I` are checked on normal forms, sixteen at a time
(`M4.row*`).  `Ski/ZK/MaskChunk.lean` uses it to build chunks with a given
value at `ζ`.
-/

namespace Circuit

open ZKF

/-- A 4×4 matrix over `F`, row `r` and column `c` in `arc`. -/
structure M4 where
  a00 : F
  a01 : F
  a02 : F
  a03 : F
  a10 : F
  a11 : F
  a12 : F
  a13 : F
  a20 : F
  a21 : F
  a22 : F
  a23 : F
  a30 : F
  a31 : F
  a32 : F
  a33 : F

/-- The determinant of a 4×4 matrix over `F`. -/

def M4.det (m : M4) : F :=
  (m.a00 * m.a11 * m.a22 * m.a33) - (m.a00 * m.a11 * m.a23 * m.a32) - (m.a00 * m.a12 * m.a21 * m.a33) + (m.a00 * m.a12 * m.a23 * m.a31) + (m.a00 * m.a13 * m.a21 * m.a32) - (m.a00 * m.a13 * m.a22 * m.a31) - (m.a01 * m.a10 * m.a22 * m.a33) + (m.a01 * m.a10 * m.a23 * m.a32) + (m.a01 * m.a12 * m.a20 * m.a33) - (m.a01 * m.a12 * m.a23 * m.a30) - (m.a01 * m.a13 * m.a20 * m.a32) + (m.a01 * m.a13 * m.a22 * m.a30) + (m.a02 * m.a10 * m.a21 * m.a33) - (m.a02 * m.a10 * m.a23 * m.a31) - (m.a02 * m.a11 * m.a20 * m.a33) + (m.a02 * m.a11 * m.a23 * m.a30) + (m.a02 * m.a13 * m.a20 * m.a31) - (m.a02 * m.a13 * m.a21 * m.a30) - (m.a03 * m.a10 * m.a21 * m.a32) + (m.a03 * m.a10 * m.a22 * m.a31) + (m.a03 * m.a11 * m.a20 * m.a32) - (m.a03 * m.a11 * m.a22 * m.a30) - (m.a03 * m.a12 * m.a20 * m.a31) + (m.a03 * m.a12 * m.a21 * m.a30)

def M4.adj00 (m : M4) : F :=
  (m.a11 * m.a22 * m.a33) - (m.a11 * m.a23 * m.a32) - (m.a12 * m.a21 * m.a33) + (m.a12 * m.a23 * m.a31) + (m.a13 * m.a21 * m.a32) - (m.a13 * m.a22 * m.a31)

def M4.adj01 (m : M4) : F :=
  0 - (m.a01 * m.a22 * m.a33) + (m.a01 * m.a23 * m.a32) + (m.a02 * m.a21 * m.a33) - (m.a02 * m.a23 * m.a31) - (m.a03 * m.a21 * m.a32) + (m.a03 * m.a22 * m.a31)

def M4.adj02 (m : M4) : F :=
  (m.a01 * m.a12 * m.a33) - (m.a01 * m.a13 * m.a32) - (m.a02 * m.a11 * m.a33) + (m.a02 * m.a13 * m.a31) + (m.a03 * m.a11 * m.a32) - (m.a03 * m.a12 * m.a31)

def M4.adj03 (m : M4) : F :=
  0 - (m.a01 * m.a12 * m.a23) + (m.a01 * m.a13 * m.a22) + (m.a02 * m.a11 * m.a23) - (m.a02 * m.a13 * m.a21) - (m.a03 * m.a11 * m.a22) + (m.a03 * m.a12 * m.a21)

def M4.adj10 (m : M4) : F :=
  0 - (m.a10 * m.a22 * m.a33) + (m.a10 * m.a23 * m.a32) + (m.a12 * m.a20 * m.a33) - (m.a12 * m.a23 * m.a30) - (m.a13 * m.a20 * m.a32) + (m.a13 * m.a22 * m.a30)

def M4.adj11 (m : M4) : F :=
  (m.a00 * m.a22 * m.a33) - (m.a00 * m.a23 * m.a32) - (m.a02 * m.a20 * m.a33) + (m.a02 * m.a23 * m.a30) + (m.a03 * m.a20 * m.a32) - (m.a03 * m.a22 * m.a30)

def M4.adj12 (m : M4) : F :=
  0 - (m.a00 * m.a12 * m.a33) + (m.a00 * m.a13 * m.a32) + (m.a02 * m.a10 * m.a33) - (m.a02 * m.a13 * m.a30) - (m.a03 * m.a10 * m.a32) + (m.a03 * m.a12 * m.a30)

def M4.adj13 (m : M4) : F :=
  (m.a00 * m.a12 * m.a23) - (m.a00 * m.a13 * m.a22) - (m.a02 * m.a10 * m.a23) + (m.a02 * m.a13 * m.a20) + (m.a03 * m.a10 * m.a22) - (m.a03 * m.a12 * m.a20)

def M4.adj20 (m : M4) : F :=
  (m.a10 * m.a21 * m.a33) - (m.a10 * m.a23 * m.a31) - (m.a11 * m.a20 * m.a33) + (m.a11 * m.a23 * m.a30) + (m.a13 * m.a20 * m.a31) - (m.a13 * m.a21 * m.a30)

def M4.adj21 (m : M4) : F :=
  0 - (m.a00 * m.a21 * m.a33) + (m.a00 * m.a23 * m.a31) + (m.a01 * m.a20 * m.a33) - (m.a01 * m.a23 * m.a30) - (m.a03 * m.a20 * m.a31) + (m.a03 * m.a21 * m.a30)

def M4.adj22 (m : M4) : F :=
  (m.a00 * m.a11 * m.a33) - (m.a00 * m.a13 * m.a31) - (m.a01 * m.a10 * m.a33) + (m.a01 * m.a13 * m.a30) + (m.a03 * m.a10 * m.a31) - (m.a03 * m.a11 * m.a30)

def M4.adj23 (m : M4) : F :=
  0 - (m.a00 * m.a11 * m.a23) + (m.a00 * m.a13 * m.a21) + (m.a01 * m.a10 * m.a23) - (m.a01 * m.a13 * m.a20) - (m.a03 * m.a10 * m.a21) + (m.a03 * m.a11 * m.a20)

def M4.adj30 (m : M4) : F :=
  0 - (m.a10 * m.a21 * m.a32) + (m.a10 * m.a22 * m.a31) + (m.a11 * m.a20 * m.a32) - (m.a11 * m.a22 * m.a30) - (m.a12 * m.a20 * m.a31) + (m.a12 * m.a21 * m.a30)

def M4.adj31 (m : M4) : F :=
  (m.a00 * m.a21 * m.a32) - (m.a00 * m.a22 * m.a31) - (m.a01 * m.a20 * m.a32) + (m.a01 * m.a22 * m.a30) + (m.a02 * m.a20 * m.a31) - (m.a02 * m.a21 * m.a30)

def M4.adj32 (m : M4) : F :=
  0 - (m.a00 * m.a11 * m.a32) + (m.a00 * m.a12 * m.a31) + (m.a01 * m.a10 * m.a32) - (m.a01 * m.a12 * m.a30) - (m.a02 * m.a10 * m.a31) + (m.a02 * m.a11 * m.a30)

def M4.adj33 (m : M4) : F :=
  (m.a00 * m.a11 * m.a22) - (m.a00 * m.a12 * m.a21) - (m.a01 * m.a10 * m.a22) + (m.a01 * m.a12 * m.a20) + (m.a02 * m.a10 * m.a21) - (m.a02 * m.a11 * m.a20)

theorem M4.row00 (m : M4) : m.a00 * m.adj00 + m.a01 * m.adj10 + m.a02 * m.adj20 + m.a03 * m.adj30 = m.det :=
  fid (e := (v 0) * ((v 5 * v 10 * v 15) - (v 5 * v 11 * v 14) - (v 6 * v 9 * v 15) + (v 6 * v 11 * v 13) + (v 7 * v 9 * v 14) - (v 7 * v 10 * v 13)) + (v 1) * (k 0 - (v 4 * v 10 * v 15) + (v 4 * v 11 * v 14) + (v 6 * v 8 * v 15) - (v 6 * v 11 * v 12) - (v 7 * v 8 * v 14) + (v 7 * v 10 * v 12)) + (v 2) * ((v 4 * v 9 * v 15) - (v 4 * v 11 * v 13) - (v 5 * v 8 * v 15) + (v 5 * v 11 * v 12) + (v 7 * v 8 * v 13) - (v 7 * v 9 * v 12)) + (v 3) * (k 0 - (v 4 * v 9 * v 14) + (v 4 * v 10 * v 13) + (v 5 * v 8 * v 14) - (v 5 * v 10 * v 12) - (v 6 * v 8 * v 13) + (v 6 * v 9 * v 12))) (e' := ((v 0 * v 5 * v 10 * v 15) - (v 0 * v 5 * v 11 * v 14) - (v 0 * v 6 * v 9 * v 15) + (v 0 * v 6 * v 11 * v 13) + (v 0 * v 7 * v 9 * v 14) - (v 0 * v 7 * v 10 * v 13) - (v 1 * v 4 * v 10 * v 15) + (v 1 * v 4 * v 11 * v 14) + (v 1 * v 6 * v 8 * v 15) - (v 1 * v 6 * v 11 * v 12) - (v 1 * v 7 * v 8 * v 14) + (v 1 * v 7 * v 10 * v 12) + (v 2 * v 4 * v 9 * v 15) - (v 2 * v 4 * v 11 * v 13) - (v 2 * v 5 * v 8 * v 15) + (v 2 * v 5 * v 11 * v 12) + (v 2 * v 7 * v 8 * v 13) - (v 2 * v 7 * v 9 * v 12) - (v 3 * v 4 * v 9 * v 14) + (v 3 * v 4 * v 10 * v 13) + (v 3 * v 5 * v 8 * v 14) - (v 3 * v 5 * v 10 * v 12) - (v 3 * v 6 * v 8 * v 13) + (v 3 * v 6 * v 9 * v 12))) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row01 (m : M4) : m.a00 * m.adj01 + m.a01 * m.adj11 + m.a02 * m.adj21 + m.a03 * m.adj31 = 0 :=
  fid (e := (v 0) * (k 0 - (v 1 * v 10 * v 15) + (v 1 * v 11 * v 14) + (v 2 * v 9 * v 15) - (v 2 * v 11 * v 13) - (v 3 * v 9 * v 14) + (v 3 * v 10 * v 13)) + (v 1) * ((v 0 * v 10 * v 15) - (v 0 * v 11 * v 14) - (v 2 * v 8 * v 15) + (v 2 * v 11 * v 12) + (v 3 * v 8 * v 14) - (v 3 * v 10 * v 12)) + (v 2) * (k 0 - (v 0 * v 9 * v 15) + (v 0 * v 11 * v 13) + (v 1 * v 8 * v 15) - (v 1 * v 11 * v 12) - (v 3 * v 8 * v 13) + (v 3 * v 9 * v 12)) + (v 3) * ((v 0 * v 9 * v 14) - (v 0 * v 10 * v 13) - (v 1 * v 8 * v 14) + (v 1 * v 10 * v 12) + (v 2 * v 8 * v 13) - (v 2 * v 9 * v 12))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row02 (m : M4) : m.a00 * m.adj02 + m.a01 * m.adj12 + m.a02 * m.adj22 + m.a03 * m.adj32 = 0 :=
  fid (e := (v 0) * ((v 1 * v 6 * v 15) - (v 1 * v 7 * v 14) - (v 2 * v 5 * v 15) + (v 2 * v 7 * v 13) + (v 3 * v 5 * v 14) - (v 3 * v 6 * v 13)) + (v 1) * (k 0 - (v 0 * v 6 * v 15) + (v 0 * v 7 * v 14) + (v 2 * v 4 * v 15) - (v 2 * v 7 * v 12) - (v 3 * v 4 * v 14) + (v 3 * v 6 * v 12)) + (v 2) * ((v 0 * v 5 * v 15) - (v 0 * v 7 * v 13) - (v 1 * v 4 * v 15) + (v 1 * v 7 * v 12) + (v 3 * v 4 * v 13) - (v 3 * v 5 * v 12)) + (v 3) * (k 0 - (v 0 * v 5 * v 14) + (v 0 * v 6 * v 13) + (v 1 * v 4 * v 14) - (v 1 * v 6 * v 12) - (v 2 * v 4 * v 13) + (v 2 * v 5 * v 12))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row03 (m : M4) : m.a00 * m.adj03 + m.a01 * m.adj13 + m.a02 * m.adj23 + m.a03 * m.adj33 = 0 :=
  fid (e := (v 0) * (k 0 - (v 1 * v 6 * v 11) + (v 1 * v 7 * v 10) + (v 2 * v 5 * v 11) - (v 2 * v 7 * v 9) - (v 3 * v 5 * v 10) + (v 3 * v 6 * v 9)) + (v 1) * ((v 0 * v 6 * v 11) - (v 0 * v 7 * v 10) - (v 2 * v 4 * v 11) + (v 2 * v 7 * v 8) + (v 3 * v 4 * v 10) - (v 3 * v 6 * v 8)) + (v 2) * (k 0 - (v 0 * v 5 * v 11) + (v 0 * v 7 * v 9) + (v 1 * v 4 * v 11) - (v 1 * v 7 * v 8) - (v 3 * v 4 * v 9) + (v 3 * v 5 * v 8)) + (v 3) * ((v 0 * v 5 * v 10) - (v 0 * v 6 * v 9) - (v 1 * v 4 * v 10) + (v 1 * v 6 * v 8) + (v 2 * v 4 * v 9) - (v 2 * v 5 * v 8))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row10 (m : M4) : m.a10 * m.adj00 + m.a11 * m.adj10 + m.a12 * m.adj20 + m.a13 * m.adj30 = 0 :=
  fid (e := (v 4) * ((v 5 * v 10 * v 15) - (v 5 * v 11 * v 14) - (v 6 * v 9 * v 15) + (v 6 * v 11 * v 13) + (v 7 * v 9 * v 14) - (v 7 * v 10 * v 13)) + (v 5) * (k 0 - (v 4 * v 10 * v 15) + (v 4 * v 11 * v 14) + (v 6 * v 8 * v 15) - (v 6 * v 11 * v 12) - (v 7 * v 8 * v 14) + (v 7 * v 10 * v 12)) + (v 6) * ((v 4 * v 9 * v 15) - (v 4 * v 11 * v 13) - (v 5 * v 8 * v 15) + (v 5 * v 11 * v 12) + (v 7 * v 8 * v 13) - (v 7 * v 9 * v 12)) + (v 7) * (k 0 - (v 4 * v 9 * v 14) + (v 4 * v 10 * v 13) + (v 5 * v 8 * v 14) - (v 5 * v 10 * v 12) - (v 6 * v 8 * v 13) + (v 6 * v 9 * v 12))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row11 (m : M4) : m.a10 * m.adj01 + m.a11 * m.adj11 + m.a12 * m.adj21 + m.a13 * m.adj31 = m.det :=
  fid (e := (v 4) * (k 0 - (v 1 * v 10 * v 15) + (v 1 * v 11 * v 14) + (v 2 * v 9 * v 15) - (v 2 * v 11 * v 13) - (v 3 * v 9 * v 14) + (v 3 * v 10 * v 13)) + (v 5) * ((v 0 * v 10 * v 15) - (v 0 * v 11 * v 14) - (v 2 * v 8 * v 15) + (v 2 * v 11 * v 12) + (v 3 * v 8 * v 14) - (v 3 * v 10 * v 12)) + (v 6) * (k 0 - (v 0 * v 9 * v 15) + (v 0 * v 11 * v 13) + (v 1 * v 8 * v 15) - (v 1 * v 11 * v 12) - (v 3 * v 8 * v 13) + (v 3 * v 9 * v 12)) + (v 7) * ((v 0 * v 9 * v 14) - (v 0 * v 10 * v 13) - (v 1 * v 8 * v 14) + (v 1 * v 10 * v 12) + (v 2 * v 8 * v 13) - (v 2 * v 9 * v 12))) (e' := ((v 0 * v 5 * v 10 * v 15) - (v 0 * v 5 * v 11 * v 14) - (v 0 * v 6 * v 9 * v 15) + (v 0 * v 6 * v 11 * v 13) + (v 0 * v 7 * v 9 * v 14) - (v 0 * v 7 * v 10 * v 13) - (v 1 * v 4 * v 10 * v 15) + (v 1 * v 4 * v 11 * v 14) + (v 1 * v 6 * v 8 * v 15) - (v 1 * v 6 * v 11 * v 12) - (v 1 * v 7 * v 8 * v 14) + (v 1 * v 7 * v 10 * v 12) + (v 2 * v 4 * v 9 * v 15) - (v 2 * v 4 * v 11 * v 13) - (v 2 * v 5 * v 8 * v 15) + (v 2 * v 5 * v 11 * v 12) + (v 2 * v 7 * v 8 * v 13) - (v 2 * v 7 * v 9 * v 12) - (v 3 * v 4 * v 9 * v 14) + (v 3 * v 4 * v 10 * v 13) + (v 3 * v 5 * v 8 * v 14) - (v 3 * v 5 * v 10 * v 12) - (v 3 * v 6 * v 8 * v 13) + (v 3 * v 6 * v 9 * v 12))) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row12 (m : M4) : m.a10 * m.adj02 + m.a11 * m.adj12 + m.a12 * m.adj22 + m.a13 * m.adj32 = 0 :=
  fid (e := (v 4) * ((v 1 * v 6 * v 15) - (v 1 * v 7 * v 14) - (v 2 * v 5 * v 15) + (v 2 * v 7 * v 13) + (v 3 * v 5 * v 14) - (v 3 * v 6 * v 13)) + (v 5) * (k 0 - (v 0 * v 6 * v 15) + (v 0 * v 7 * v 14) + (v 2 * v 4 * v 15) - (v 2 * v 7 * v 12) - (v 3 * v 4 * v 14) + (v 3 * v 6 * v 12)) + (v 6) * ((v 0 * v 5 * v 15) - (v 0 * v 7 * v 13) - (v 1 * v 4 * v 15) + (v 1 * v 7 * v 12) + (v 3 * v 4 * v 13) - (v 3 * v 5 * v 12)) + (v 7) * (k 0 - (v 0 * v 5 * v 14) + (v 0 * v 6 * v 13) + (v 1 * v 4 * v 14) - (v 1 * v 6 * v 12) - (v 2 * v 4 * v 13) + (v 2 * v 5 * v 12))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row13 (m : M4) : m.a10 * m.adj03 + m.a11 * m.adj13 + m.a12 * m.adj23 + m.a13 * m.adj33 = 0 :=
  fid (e := (v 4) * (k 0 - (v 1 * v 6 * v 11) + (v 1 * v 7 * v 10) + (v 2 * v 5 * v 11) - (v 2 * v 7 * v 9) - (v 3 * v 5 * v 10) + (v 3 * v 6 * v 9)) + (v 5) * ((v 0 * v 6 * v 11) - (v 0 * v 7 * v 10) - (v 2 * v 4 * v 11) + (v 2 * v 7 * v 8) + (v 3 * v 4 * v 10) - (v 3 * v 6 * v 8)) + (v 6) * (k 0 - (v 0 * v 5 * v 11) + (v 0 * v 7 * v 9) + (v 1 * v 4 * v 11) - (v 1 * v 7 * v 8) - (v 3 * v 4 * v 9) + (v 3 * v 5 * v 8)) + (v 7) * ((v 0 * v 5 * v 10) - (v 0 * v 6 * v 9) - (v 1 * v 4 * v 10) + (v 1 * v 6 * v 8) + (v 2 * v 4 * v 9) - (v 2 * v 5 * v 8))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row20 (m : M4) : m.a20 * m.adj00 + m.a21 * m.adj10 + m.a22 * m.adj20 + m.a23 * m.adj30 = 0 :=
  fid (e := (v 8) * ((v 5 * v 10 * v 15) - (v 5 * v 11 * v 14) - (v 6 * v 9 * v 15) + (v 6 * v 11 * v 13) + (v 7 * v 9 * v 14) - (v 7 * v 10 * v 13)) + (v 9) * (k 0 - (v 4 * v 10 * v 15) + (v 4 * v 11 * v 14) + (v 6 * v 8 * v 15) - (v 6 * v 11 * v 12) - (v 7 * v 8 * v 14) + (v 7 * v 10 * v 12)) + (v 10) * ((v 4 * v 9 * v 15) - (v 4 * v 11 * v 13) - (v 5 * v 8 * v 15) + (v 5 * v 11 * v 12) + (v 7 * v 8 * v 13) - (v 7 * v 9 * v 12)) + (v 11) * (k 0 - (v 4 * v 9 * v 14) + (v 4 * v 10 * v 13) + (v 5 * v 8 * v 14) - (v 5 * v 10 * v 12) - (v 6 * v 8 * v 13) + (v 6 * v 9 * v 12))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row21 (m : M4) : m.a20 * m.adj01 + m.a21 * m.adj11 + m.a22 * m.adj21 + m.a23 * m.adj31 = 0 :=
  fid (e := (v 8) * (k 0 - (v 1 * v 10 * v 15) + (v 1 * v 11 * v 14) + (v 2 * v 9 * v 15) - (v 2 * v 11 * v 13) - (v 3 * v 9 * v 14) + (v 3 * v 10 * v 13)) + (v 9) * ((v 0 * v 10 * v 15) - (v 0 * v 11 * v 14) - (v 2 * v 8 * v 15) + (v 2 * v 11 * v 12) + (v 3 * v 8 * v 14) - (v 3 * v 10 * v 12)) + (v 10) * (k 0 - (v 0 * v 9 * v 15) + (v 0 * v 11 * v 13) + (v 1 * v 8 * v 15) - (v 1 * v 11 * v 12) - (v 3 * v 8 * v 13) + (v 3 * v 9 * v 12)) + (v 11) * ((v 0 * v 9 * v 14) - (v 0 * v 10 * v 13) - (v 1 * v 8 * v 14) + (v 1 * v 10 * v 12) + (v 2 * v 8 * v 13) - (v 2 * v 9 * v 12))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row22 (m : M4) : m.a20 * m.adj02 + m.a21 * m.adj12 + m.a22 * m.adj22 + m.a23 * m.adj32 = m.det :=
  fid (e := (v 8) * ((v 1 * v 6 * v 15) - (v 1 * v 7 * v 14) - (v 2 * v 5 * v 15) + (v 2 * v 7 * v 13) + (v 3 * v 5 * v 14) - (v 3 * v 6 * v 13)) + (v 9) * (k 0 - (v 0 * v 6 * v 15) + (v 0 * v 7 * v 14) + (v 2 * v 4 * v 15) - (v 2 * v 7 * v 12) - (v 3 * v 4 * v 14) + (v 3 * v 6 * v 12)) + (v 10) * ((v 0 * v 5 * v 15) - (v 0 * v 7 * v 13) - (v 1 * v 4 * v 15) + (v 1 * v 7 * v 12) + (v 3 * v 4 * v 13) - (v 3 * v 5 * v 12)) + (v 11) * (k 0 - (v 0 * v 5 * v 14) + (v 0 * v 6 * v 13) + (v 1 * v 4 * v 14) - (v 1 * v 6 * v 12) - (v 2 * v 4 * v 13) + (v 2 * v 5 * v 12))) (e' := ((v 0 * v 5 * v 10 * v 15) - (v 0 * v 5 * v 11 * v 14) - (v 0 * v 6 * v 9 * v 15) + (v 0 * v 6 * v 11 * v 13) + (v 0 * v 7 * v 9 * v 14) - (v 0 * v 7 * v 10 * v 13) - (v 1 * v 4 * v 10 * v 15) + (v 1 * v 4 * v 11 * v 14) + (v 1 * v 6 * v 8 * v 15) - (v 1 * v 6 * v 11 * v 12) - (v 1 * v 7 * v 8 * v 14) + (v 1 * v 7 * v 10 * v 12) + (v 2 * v 4 * v 9 * v 15) - (v 2 * v 4 * v 11 * v 13) - (v 2 * v 5 * v 8 * v 15) + (v 2 * v 5 * v 11 * v 12) + (v 2 * v 7 * v 8 * v 13) - (v 2 * v 7 * v 9 * v 12) - (v 3 * v 4 * v 9 * v 14) + (v 3 * v 4 * v 10 * v 13) + (v 3 * v 5 * v 8 * v 14) - (v 3 * v 5 * v 10 * v 12) - (v 3 * v 6 * v 8 * v 13) + (v 3 * v 6 * v 9 * v 12))) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row23 (m : M4) : m.a20 * m.adj03 + m.a21 * m.adj13 + m.a22 * m.adj23 + m.a23 * m.adj33 = 0 :=
  fid (e := (v 8) * (k 0 - (v 1 * v 6 * v 11) + (v 1 * v 7 * v 10) + (v 2 * v 5 * v 11) - (v 2 * v 7 * v 9) - (v 3 * v 5 * v 10) + (v 3 * v 6 * v 9)) + (v 9) * ((v 0 * v 6 * v 11) - (v 0 * v 7 * v 10) - (v 2 * v 4 * v 11) + (v 2 * v 7 * v 8) + (v 3 * v 4 * v 10) - (v 3 * v 6 * v 8)) + (v 10) * (k 0 - (v 0 * v 5 * v 11) + (v 0 * v 7 * v 9) + (v 1 * v 4 * v 11) - (v 1 * v 7 * v 8) - (v 3 * v 4 * v 9) + (v 3 * v 5 * v 8)) + (v 11) * ((v 0 * v 5 * v 10) - (v 0 * v 6 * v 9) - (v 1 * v 4 * v 10) + (v 1 * v 6 * v 8) + (v 2 * v 4 * v 9) - (v 2 * v 5 * v 8))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row30 (m : M4) : m.a30 * m.adj00 + m.a31 * m.adj10 + m.a32 * m.adj20 + m.a33 * m.adj30 = 0 :=
  fid (e := (v 12) * ((v 5 * v 10 * v 15) - (v 5 * v 11 * v 14) - (v 6 * v 9 * v 15) + (v 6 * v 11 * v 13) + (v 7 * v 9 * v 14) - (v 7 * v 10 * v 13)) + (v 13) * (k 0 - (v 4 * v 10 * v 15) + (v 4 * v 11 * v 14) + (v 6 * v 8 * v 15) - (v 6 * v 11 * v 12) - (v 7 * v 8 * v 14) + (v 7 * v 10 * v 12)) + (v 14) * ((v 4 * v 9 * v 15) - (v 4 * v 11 * v 13) - (v 5 * v 8 * v 15) + (v 5 * v 11 * v 12) + (v 7 * v 8 * v 13) - (v 7 * v 9 * v 12)) + (v 15) * (k 0 - (v 4 * v 9 * v 14) + (v 4 * v 10 * v 13) + (v 5 * v 8 * v 14) - (v 5 * v 10 * v 12) - (v 6 * v 8 * v 13) + (v 6 * v 9 * v 12))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row31 (m : M4) : m.a30 * m.adj01 + m.a31 * m.adj11 + m.a32 * m.adj21 + m.a33 * m.adj31 = 0 :=
  fid (e := (v 12) * (k 0 - (v 1 * v 10 * v 15) + (v 1 * v 11 * v 14) + (v 2 * v 9 * v 15) - (v 2 * v 11 * v 13) - (v 3 * v 9 * v 14) + (v 3 * v 10 * v 13)) + (v 13) * ((v 0 * v 10 * v 15) - (v 0 * v 11 * v 14) - (v 2 * v 8 * v 15) + (v 2 * v 11 * v 12) + (v 3 * v 8 * v 14) - (v 3 * v 10 * v 12)) + (v 14) * (k 0 - (v 0 * v 9 * v 15) + (v 0 * v 11 * v 13) + (v 1 * v 8 * v 15) - (v 1 * v 11 * v 12) - (v 3 * v 8 * v 13) + (v 3 * v 9 * v 12)) + (v 15) * ((v 0 * v 9 * v 14) - (v 0 * v 10 * v 13) - (v 1 * v 8 * v 14) + (v 1 * v 10 * v 12) + (v 2 * v 8 * v 13) - (v 2 * v 9 * v 12))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row32 (m : M4) : m.a30 * m.adj02 + m.a31 * m.adj12 + m.a32 * m.adj22 + m.a33 * m.adj32 = 0 :=
  fid (e := (v 12) * ((v 1 * v 6 * v 15) - (v 1 * v 7 * v 14) - (v 2 * v 5 * v 15) + (v 2 * v 7 * v 13) + (v 3 * v 5 * v 14) - (v 3 * v 6 * v 13)) + (v 13) * (k 0 - (v 0 * v 6 * v 15) + (v 0 * v 7 * v 14) + (v 2 * v 4 * v 15) - (v 2 * v 7 * v 12) - (v 3 * v 4 * v 14) + (v 3 * v 6 * v 12)) + (v 14) * ((v 0 * v 5 * v 15) - (v 0 * v 7 * v 13) - (v 1 * v 4 * v 15) + (v 1 * v 7 * v 12) + (v 3 * v 4 * v 13) - (v 3 * v 5 * v 12)) + (v 15) * (k 0 - (v 0 * v 5 * v 14) + (v 0 * v 6 * v 13) + (v 1 * v 4 * v 14) - (v 1 * v 6 * v 12) - (v 2 * v 4 * v 13) + (v 2 * v 5 * v 12))) (e' := k 0) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

theorem M4.row33 (m : M4) : m.a30 * m.adj03 + m.a31 * m.adj13 + m.a32 * m.adj23 + m.a33 * m.adj33 = m.det :=
  fid (e := (v 12) * (k 0 - (v 1 * v 6 * v 11) + (v 1 * v 7 * v 10) + (v 2 * v 5 * v 11) - (v 2 * v 7 * v 9) - (v 3 * v 5 * v 10) + (v 3 * v 6 * v 9)) + (v 13) * ((v 0 * v 6 * v 11) - (v 0 * v 7 * v 10) - (v 2 * v 4 * v 11) + (v 2 * v 7 * v 8) + (v 3 * v 4 * v 10) - (v 3 * v 6 * v 8)) + (v 14) * (k 0 - (v 0 * v 5 * v 11) + (v 0 * v 7 * v 9) + (v 1 * v 4 * v 11) - (v 1 * v 7 * v 8) - (v 3 * v 4 * v 9) + (v 3 * v 5 * v 8)) + (v 15) * ((v 0 * v 5 * v 10) - (v 0 * v 6 * v 9) - (v 1 * v 4 * v 10) + (v 1 * v 6 * v 8) + (v 2 * v 4 * v 9) - (v 2 * v 5 * v 8))) (e' := ((v 0 * v 5 * v 10 * v 15) - (v 0 * v 5 * v 11 * v 14) - (v 0 * v 6 * v 9 * v 15) + (v 0 * v 6 * v 11 * v 13) + (v 0 * v 7 * v 9 * v 14) - (v 0 * v 7 * v 10 * v 13) - (v 1 * v 4 * v 10 * v 15) + (v 1 * v 4 * v 11 * v 14) + (v 1 * v 6 * v 8 * v 15) - (v 1 * v 6 * v 11 * v 12) - (v 1 * v 7 * v 8 * v 14) + (v 1 * v 7 * v 10 * v 12) + (v 2 * v 4 * v 9 * v 15) - (v 2 * v 4 * v 11 * v 13) - (v 2 * v 5 * v 8 * v 15) + (v 2 * v 5 * v 11 * v 12) + (v 2 * v 7 * v 8 * v 13) - (v 2 * v 7 * v 9 * v 12) - (v 3 * v 4 * v 9 * v 14) + (v 3 * v 4 * v 10 * v 13) + (v 3 * v 5 * v 8 * v 14) - (v 3 * v 5 * v 10 * v 12) - (v 3 * v 6 * v 8 * v 13) + (v 3 * v 6 * v 9 * v 12))) (by decide) [m.a00, m.a01, m.a02, m.a03, m.a10, m.a11, m.a12, m.a13, m.a20, m.a21, m.a22, m.a23, m.a30, m.a31, m.a32, m.a33]

/-- The solution of `m · a = e`, by the adjugate. -/
def M4.solve (m : M4) (e0 e1 e2 e3 : F) : List F :=
  [finv m.det * (m.adj00 * e0 + m.adj01 * e1 + m.adj02 * e2 + m.adj03 * e3), finv m.det * (m.adj10 * e0 + m.adj11 * e1 + m.adj12 * e2 + m.adj13 * e3), finv m.det * (m.adj20 * e0 + m.adj21 * e1 + m.adj22 * e2 + m.adj23 * e3), finv m.det * (m.adj30 * e0 + m.adj31 * e1 + m.adj32 * e2 + m.adj33 * e3)]

theorem M4.comp0 (m : M4) (fi e0 e1 e2 e3 : F) :
    (fi * (m.adj00 * e0 + m.adj01 * e1 + m.adj02 * e2 + m.adj03 * e3)) * m.a00 + (fi * (m.adj10 * e0 + m.adj11 * e1 + m.adj12 * e2 + m.adj13 * e3)) * m.a01 + (fi * (m.adj20 * e0 + m.adj21 * e1 + m.adj22 * e2 + m.adj23 * e3)) * m.a02 + (fi * (m.adj30 * e0 + m.adj31 * e1 + m.adj32 * e2 + m.adj33 * e3)) * m.a03 =
      fi * ((m.a00 * m.adj00 + m.a01 * m.adj10 + m.a02 * m.adj20 + m.a03 * m.adj30) * e0 + (m.a00 * m.adj01 + m.a01 * m.adj11 + m.a02 * m.adj21 + m.a03 * m.adj31) * e1 + (m.a00 * m.adj02 + m.a01 * m.adj12 + m.a02 * m.adj22 + m.a03 * m.adj32) * e2 + (m.a00 * m.adj03 + m.a01 * m.adj13 + m.a02 * m.adj23 + m.a03 * m.adj33) * e3) :=
  fid (e := (v 20 * (v 4 * v 21 + v 5 * v 22 + v 6 * v 23 + v 7 * v 24)) * v 0 + (v 20 * (v 8 * v 21 + v 9 * v 22 + v 10 * v 23 + v 11 * v 24)) * v 1 + (v 20 * (v 12 * v 21 + v 13 * v 22 + v 14 * v 23 + v 15 * v 24)) * v 2 + (v 20 * (v 16 * v 21 + v 17 * v 22 + v 18 * v 23 + v 19 * v 24)) * v 3) (e' := v 20 * ((v 0 * v 4 + v 1 * v 8 + v 2 * v 12 + v 3 * v 16) * v 21 + (v 0 * v 5 + v 1 * v 9 + v 2 * v 13 + v 3 * v 17) * v 22 + (v 0 * v 6 + v 1 * v 10 + v 2 * v 14 + v 3 * v 18) * v 23 + (v 0 * v 7 + v 1 * v 11 + v 2 * v 15 + v 3 * v 19) * v 24)) (by decide)
    [m.a00, m.a01, m.a02, m.a03, m.adj00, m.adj01, m.adj02, m.adj03, m.adj10, m.adj11, m.adj12, m.adj13, m.adj20, m.adj21, m.adj22, m.adj23, m.adj30, m.adj31, m.adj32, m.adj33, fi, e0, e1, e2, e3]

theorem M4.fin0 (fi d e0 e1 e2 e3 : F) : fi * (d * e0 + 0 * e1 + 0 * e2 + 0 * e3) = (fi * d) * e0 :=
  fid (e := v 5 * (v 0 * v 1 + k 0 * v 2 + k 0 * v 3 + k 0 * v 4)) (e' := (v 5 * v 0) * v 1) (by decide) [d, e0, e1, e2, e3, fi]

theorem M4.sol0 (m : M4) (hd : m.det ≠ 0) (e0 e1 e2 e3 : F) :
    (finv m.det * (m.adj00 * e0 + m.adj01 * e1 + m.adj02 * e2 + m.adj03 * e3)) * m.a00 + (finv m.det * (m.adj10 * e0 + m.adj11 * e1 + m.adj12 * e2 + m.adj13 * e3)) * m.a01 + (finv m.det * (m.adj20 * e0 + m.adj21 * e1 + m.adj22 * e2 + m.adj23 * e3)) * m.a02 + (finv m.det * (m.adj30 * e0 + m.adj31 * e1 + m.adj32 * e2 + m.adj33 * e3)) * m.a03 = e0 := by
  rw [M4.comp0, M4.row00, M4.row01, M4.row02, M4.row03]
  rw [M4.fin0, finv_mul hd, one_mul']

theorem M4.comp1 (m : M4) (fi e0 e1 e2 e3 : F) :
    (fi * (m.adj00 * e0 + m.adj01 * e1 + m.adj02 * e2 + m.adj03 * e3)) * m.a10 + (fi * (m.adj10 * e0 + m.adj11 * e1 + m.adj12 * e2 + m.adj13 * e3)) * m.a11 + (fi * (m.adj20 * e0 + m.adj21 * e1 + m.adj22 * e2 + m.adj23 * e3)) * m.a12 + (fi * (m.adj30 * e0 + m.adj31 * e1 + m.adj32 * e2 + m.adj33 * e3)) * m.a13 =
      fi * ((m.a10 * m.adj00 + m.a11 * m.adj10 + m.a12 * m.adj20 + m.a13 * m.adj30) * e0 + (m.a10 * m.adj01 + m.a11 * m.adj11 + m.a12 * m.adj21 + m.a13 * m.adj31) * e1 + (m.a10 * m.adj02 + m.a11 * m.adj12 + m.a12 * m.adj22 + m.a13 * m.adj32) * e2 + (m.a10 * m.adj03 + m.a11 * m.adj13 + m.a12 * m.adj23 + m.a13 * m.adj33) * e3) :=
  fid (e := (v 20 * (v 4 * v 21 + v 5 * v 22 + v 6 * v 23 + v 7 * v 24)) * v 0 + (v 20 * (v 8 * v 21 + v 9 * v 22 + v 10 * v 23 + v 11 * v 24)) * v 1 + (v 20 * (v 12 * v 21 + v 13 * v 22 + v 14 * v 23 + v 15 * v 24)) * v 2 + (v 20 * (v 16 * v 21 + v 17 * v 22 + v 18 * v 23 + v 19 * v 24)) * v 3) (e' := v 20 * ((v 0 * v 4 + v 1 * v 8 + v 2 * v 12 + v 3 * v 16) * v 21 + (v 0 * v 5 + v 1 * v 9 + v 2 * v 13 + v 3 * v 17) * v 22 + (v 0 * v 6 + v 1 * v 10 + v 2 * v 14 + v 3 * v 18) * v 23 + (v 0 * v 7 + v 1 * v 11 + v 2 * v 15 + v 3 * v 19) * v 24)) (by decide)
    [m.a10, m.a11, m.a12, m.a13, m.adj00, m.adj01, m.adj02, m.adj03, m.adj10, m.adj11, m.adj12, m.adj13, m.adj20, m.adj21, m.adj22, m.adj23, m.adj30, m.adj31, m.adj32, m.adj33, fi, e0, e1, e2, e3]

theorem M4.fin1 (fi d e0 e1 e2 e3 : F) : fi * (0 * e0 + d * e1 + 0 * e2 + 0 * e3) = (fi * d) * e1 :=
  fid (e := v 5 * (k 0 * v 1 + v 0 * v 2 + k 0 * v 3 + k 0 * v 4)) (e' := (v 5 * v 0) * v 2) (by decide) [d, e0, e1, e2, e3, fi]

theorem M4.sol1 (m : M4) (hd : m.det ≠ 0) (e0 e1 e2 e3 : F) :
    (finv m.det * (m.adj00 * e0 + m.adj01 * e1 + m.adj02 * e2 + m.adj03 * e3)) * m.a10 + (finv m.det * (m.adj10 * e0 + m.adj11 * e1 + m.adj12 * e2 + m.adj13 * e3)) * m.a11 + (finv m.det * (m.adj20 * e0 + m.adj21 * e1 + m.adj22 * e2 + m.adj23 * e3)) * m.a12 + (finv m.det * (m.adj30 * e0 + m.adj31 * e1 + m.adj32 * e2 + m.adj33 * e3)) * m.a13 = e1 := by
  rw [M4.comp1, M4.row10, M4.row11, M4.row12, M4.row13]
  rw [M4.fin1, finv_mul hd, one_mul']

theorem M4.comp2 (m : M4) (fi e0 e1 e2 e3 : F) :
    (fi * (m.adj00 * e0 + m.adj01 * e1 + m.adj02 * e2 + m.adj03 * e3)) * m.a20 + (fi * (m.adj10 * e0 + m.adj11 * e1 + m.adj12 * e2 + m.adj13 * e3)) * m.a21 + (fi * (m.adj20 * e0 + m.adj21 * e1 + m.adj22 * e2 + m.adj23 * e3)) * m.a22 + (fi * (m.adj30 * e0 + m.adj31 * e1 + m.adj32 * e2 + m.adj33 * e3)) * m.a23 =
      fi * ((m.a20 * m.adj00 + m.a21 * m.adj10 + m.a22 * m.adj20 + m.a23 * m.adj30) * e0 + (m.a20 * m.adj01 + m.a21 * m.adj11 + m.a22 * m.adj21 + m.a23 * m.adj31) * e1 + (m.a20 * m.adj02 + m.a21 * m.adj12 + m.a22 * m.adj22 + m.a23 * m.adj32) * e2 + (m.a20 * m.adj03 + m.a21 * m.adj13 + m.a22 * m.adj23 + m.a23 * m.adj33) * e3) :=
  fid (e := (v 20 * (v 4 * v 21 + v 5 * v 22 + v 6 * v 23 + v 7 * v 24)) * v 0 + (v 20 * (v 8 * v 21 + v 9 * v 22 + v 10 * v 23 + v 11 * v 24)) * v 1 + (v 20 * (v 12 * v 21 + v 13 * v 22 + v 14 * v 23 + v 15 * v 24)) * v 2 + (v 20 * (v 16 * v 21 + v 17 * v 22 + v 18 * v 23 + v 19 * v 24)) * v 3) (e' := v 20 * ((v 0 * v 4 + v 1 * v 8 + v 2 * v 12 + v 3 * v 16) * v 21 + (v 0 * v 5 + v 1 * v 9 + v 2 * v 13 + v 3 * v 17) * v 22 + (v 0 * v 6 + v 1 * v 10 + v 2 * v 14 + v 3 * v 18) * v 23 + (v 0 * v 7 + v 1 * v 11 + v 2 * v 15 + v 3 * v 19) * v 24)) (by decide)
    [m.a20, m.a21, m.a22, m.a23, m.adj00, m.adj01, m.adj02, m.adj03, m.adj10, m.adj11, m.adj12, m.adj13, m.adj20, m.adj21, m.adj22, m.adj23, m.adj30, m.adj31, m.adj32, m.adj33, fi, e0, e1, e2, e3]

theorem M4.fin2 (fi d e0 e1 e2 e3 : F) : fi * (0 * e0 + 0 * e1 + d * e2 + 0 * e3) = (fi * d) * e2 :=
  fid (e := v 5 * (k 0 * v 1 + k 0 * v 2 + v 0 * v 3 + k 0 * v 4)) (e' := (v 5 * v 0) * v 3) (by decide) [d, e0, e1, e2, e3, fi]

theorem M4.sol2 (m : M4) (hd : m.det ≠ 0) (e0 e1 e2 e3 : F) :
    (finv m.det * (m.adj00 * e0 + m.adj01 * e1 + m.adj02 * e2 + m.adj03 * e3)) * m.a20 + (finv m.det * (m.adj10 * e0 + m.adj11 * e1 + m.adj12 * e2 + m.adj13 * e3)) * m.a21 + (finv m.det * (m.adj20 * e0 + m.adj21 * e1 + m.adj22 * e2 + m.adj23 * e3)) * m.a22 + (finv m.det * (m.adj30 * e0 + m.adj31 * e1 + m.adj32 * e2 + m.adj33 * e3)) * m.a23 = e2 := by
  rw [M4.comp2, M4.row20, M4.row21, M4.row22, M4.row23]
  rw [M4.fin2, finv_mul hd, one_mul']

theorem M4.comp3 (m : M4) (fi e0 e1 e2 e3 : F) :
    (fi * (m.adj00 * e0 + m.adj01 * e1 + m.adj02 * e2 + m.adj03 * e3)) * m.a30 + (fi * (m.adj10 * e0 + m.adj11 * e1 + m.adj12 * e2 + m.adj13 * e3)) * m.a31 + (fi * (m.adj20 * e0 + m.adj21 * e1 + m.adj22 * e2 + m.adj23 * e3)) * m.a32 + (fi * (m.adj30 * e0 + m.adj31 * e1 + m.adj32 * e2 + m.adj33 * e3)) * m.a33 =
      fi * ((m.a30 * m.adj00 + m.a31 * m.adj10 + m.a32 * m.adj20 + m.a33 * m.adj30) * e0 + (m.a30 * m.adj01 + m.a31 * m.adj11 + m.a32 * m.adj21 + m.a33 * m.adj31) * e1 + (m.a30 * m.adj02 + m.a31 * m.adj12 + m.a32 * m.adj22 + m.a33 * m.adj32) * e2 + (m.a30 * m.adj03 + m.a31 * m.adj13 + m.a32 * m.adj23 + m.a33 * m.adj33) * e3) :=
  fid (e := (v 20 * (v 4 * v 21 + v 5 * v 22 + v 6 * v 23 + v 7 * v 24)) * v 0 + (v 20 * (v 8 * v 21 + v 9 * v 22 + v 10 * v 23 + v 11 * v 24)) * v 1 + (v 20 * (v 12 * v 21 + v 13 * v 22 + v 14 * v 23 + v 15 * v 24)) * v 2 + (v 20 * (v 16 * v 21 + v 17 * v 22 + v 18 * v 23 + v 19 * v 24)) * v 3) (e' := v 20 * ((v 0 * v 4 + v 1 * v 8 + v 2 * v 12 + v 3 * v 16) * v 21 + (v 0 * v 5 + v 1 * v 9 + v 2 * v 13 + v 3 * v 17) * v 22 + (v 0 * v 6 + v 1 * v 10 + v 2 * v 14 + v 3 * v 18) * v 23 + (v 0 * v 7 + v 1 * v 11 + v 2 * v 15 + v 3 * v 19) * v 24)) (by decide)
    [m.a30, m.a31, m.a32, m.a33, m.adj00, m.adj01, m.adj02, m.adj03, m.adj10, m.adj11, m.adj12, m.adj13, m.adj20, m.adj21, m.adj22, m.adj23, m.adj30, m.adj31, m.adj32, m.adj33, fi, e0, e1, e2, e3]

theorem M4.fin3 (fi d e0 e1 e2 e3 : F) : fi * (0 * e0 + 0 * e1 + 0 * e2 + d * e3) = (fi * d) * e3 :=
  fid (e := v 5 * (k 0 * v 1 + k 0 * v 2 + k 0 * v 3 + v 0 * v 4)) (e' := (v 5 * v 0) * v 4) (by decide) [d, e0, e1, e2, e3, fi]

theorem M4.sol3 (m : M4) (hd : m.det ≠ 0) (e0 e1 e2 e3 : F) :
    (finv m.det * (m.adj00 * e0 + m.adj01 * e1 + m.adj02 * e2 + m.adj03 * e3)) * m.a30 + (finv m.det * (m.adj10 * e0 + m.adj11 * e1 + m.adj12 * e2 + m.adj13 * e3)) * m.a31 + (finv m.det * (m.adj20 * e0 + m.adj21 * e1 + m.adj22 * e2 + m.adj23 * e3)) * m.a32 + (finv m.det * (m.adj30 * e0 + m.adj31 * e1 + m.adj32 * e2 + m.adj33 * e3)) * m.a33 = e3 := by
  rw [M4.comp3, M4.row30, M4.row31, M4.row32, M4.row33]
  rw [M4.fin3, finv_mul hd, one_mul']

-- ---------------------------------------------------------------------------
-- A polynomial over `F` through one point of the extension
-- ---------------------------------------------------------------------------

/-- The powers `1, z, z², z³` as columns, coordinates as rows. -/
def mz (z : EF) : M4 :=
  ⟨EF.one.x0, z.x0, (z.mul z).x0, ((z.mul z).mul z).x0,
   EF.one.x1, z.x1, (z.mul z).x1, ((z.mul z).mul z).x1,
   EF.one.x2, z.x2, (z.mul z).x2, ((z.mul z).mul z).x2,
   EF.one.x3, z.x3, (z.mul z).x3, ((z.mul z).mul z).x3⟩

set_option maxRecDepth 20000 in
theorem hornerE (z B0 B1 B2 B3 : EF) :
    B0.add (z.mul (B1.add (z.mul (B2.add (z.mul (B3.add (z.mul EF.zero))))))) =
      ((B0.mul EF.one).add (B1.mul z)).add ((B2.mul (z.mul z)).add (B3.mul ((z.mul z).mul z))) :=
  Q.eq_of_norm
    (p := (Q.var 1).add ((Q.var 0).mul ((Q.var 2).add ((Q.var 0).mul ((Q.var 3).add ((Q.var 0).mul
      ((Q.var 4).add ((Q.var 0).mul (⟨k 0, k 0, k 0, k 0⟩ : Q)))))))))
    (q := (((Q.var 1).mul (⟨k 1, k 0, k 0, k 0⟩ : Q)).add ((Q.var 2).mul (Q.var 0))).add
      (((Q.var 3).mul ((Q.var 0).mul (Q.var 0))).add ((Q.var 4).mul (((Q.var 0).mul (Q.var 0)).mul (Q.var 0)))))
    (by decide) (env8 z B0 B1 B2 B3 EF.zero EF.zero EF.zero)

theorem fvalE4 (z : EF) (b0 b1 b2 b3 : F) :
    fvalE z [b0, b1, b2, b3] = (((EF.ofF b0).mul EF.one).add ((EF.ofF b1).mul z)).add
      (((EF.ofF b2).mul (z.mul z)).add ((EF.ofF b3).mul ((z.mul z).mul z))) := by
  rw [fvalE_cons, fvalE_cons, fvalE_cons, fvalE_cons, show fvalE z [] = EF.zero from rfl, hornerE]

theorem ofF_mul_x0 (b : F) (y : EF) : ((EF.ofF b).mul y).x0 = b * y.x0 :=
  fid (e := v 0 * v 1 + k W11 * (k 0 * v 4 + k 0 * v 3 + k 0 * v 2)) (e' := v 0 * v 1) (by decide)
    [b, y.x0, y.x1, y.x2, y.x3]

theorem ofF_mul_x1 (b : F) (y : EF) : ((EF.ofF b).mul y).x1 = b * y.x1 :=
  fid (e := v 0 * v 2 + k 0 * v 1 + k W11 * (k 0 * v 4 + k 0 * v 3)) (e' := v 0 * v 2) (by decide)
    [b, y.x0, y.x1, y.x2, y.x3]

theorem ofF_mul_x2 (b : F) (y : EF) : ((EF.ofF b).mul y).x2 = b * y.x2 :=
  fid (e := v 0 * v 3 + k 0 * v 2 + k 0 * v 1 + k W11 * (k 0 * v 4)) (e' := v 0 * v 3) (by decide)
    [b, y.x0, y.x1, y.x2, y.x3]

theorem ofF_mul_x3 (b : F) (y : EF) : ((EF.ofF b).mul y).x3 = b * y.x3 :=
  fid (e := v 0 * v 4 + k 0 * v 3 + k 0 * v 2 + k 0 * v 1) (e' := v 0 * v 4) (by decide)
    [b, y.x0, y.x1, y.x2, y.x3]

theorem add_x0 (x y : EF) : (x.add y).x0 = x.x0 + y.x0 := rfl
theorem add_x1 (x y : EF) : (x.add y).x1 = x.x1 + y.x1 := rfl
theorem add_x2 (x y : EF) : (x.add y).x2 = x.x2 + y.x2 := rfl
theorem add_x3 (x y : EF) : (x.add y).x3 = x.x3 + y.x3 := rfl

theorem add4' (a b c d : F) : (a + b) + (c + d) = a + b + c + d :=
  fid (e := (v 0 + v 1) + (v 2 + v 3)) (e' := v 0 + v 1 + v 2 + v 3) (by decide) [a, b, c, d]

/-- **Four coefficients over `F` reach any point of the extension at `z`**,
    when the powers `1, z, z², z³` are independent over `F`
    (`(mz z).det ≠ 0`, which holds when `z` generates the extension). -/
theorem solve_spec (z : EF) (hd : (mz z).det ≠ 0) (e : EF) :
    fvalE z ((mz z).solve e.x0 e.x1 e.x2 e.x3) = e := by
  unfold M4.solve
  rw [fvalE4]
  refine EF.ext ?_ ?_ ?_ ?_
  · rw [add_x0, add_x0, add_x0, ofF_mul_x0, ofF_mul_x0, ofF_mul_x0, ofF_mul_x0, add4']
    exact M4.sol0 (mz z) hd _ _ _ _
  · rw [add_x1, add_x1, add_x1, ofF_mul_x1, ofF_mul_x1, ofF_mul_x1, ofF_mul_x1, add4']
    exact M4.sol1 (mz z) hd _ _ _ _
  · rw [add_x2, add_x2, add_x2, ofF_mul_x2, ofF_mul_x2, ofF_mul_x2, ofF_mul_x2, add4']
    exact M4.sol2 (mz z) hd _ _ _ _
  · rw [add_x3, add_x3, add_x3, ofF_mul_x3, ofF_mul_x3, ofF_mul_x3, ofF_mul_x3, add4']
    exact M4.sol3 (mz z) hd _ _ _ _

theorem solve_length (m : M4) (e0 e1 e2 e3 : F) : (m.solve e0 e1 e2 e3).length = 4 := rfl

/-- **The hypothesis holds**: at the extension's generator `w`, the powers
    are the basis, and the determinant is one. -/
theorem mz_gen_det : (mz ⟨0, 1, 0, 0⟩).det ≠ 0 := by decide

end Circuit
