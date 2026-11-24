import GaugeFieldConstruction.Radius
import GaugeFieldConstruction.Camera
import GaugeFieldConstruction.CrossClock

/-!
# Raster for reflection matrix. Money values no normal in them.
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.Vouchers
namespace Credit
def silver (z : Credit): Credit:=⟨z.re,-z.im⟩
def zn (i : ℤ) : Credit := ⟨i,0⟩
lemma cc (z : Credit) : (silver z).money=star z.money:= by simp [silver,money,mul_comm]
lemma zn_pay (i) : (zn i).money=i:=by simp [zn,money]
def sum (s : List Credit) := s.foldr (· + ·) 0
lemma sum_money (s : List Credit) : (sum s).money=(s.map money).sum := by
  induction s with
  | nil=> exact zero_c
  | cons a s ih => rw [show sum (a::s)=a+sum s from rfl, plus, ih]; rfl
end Credit
end YM.GaugeFieldConstruction.Vouchers
namespace YM.GaugeFieldConstruction.Wick.Raster
open Vouchers Credit Gap Cauchy Row Function Complex Finset Phys Mirror
open YM.Maxwell (normal Green)
open scoped Topology BigOperators

local notation "A" => Module.End ℂ SmoothGap
noncomputable def tilt (n : MI) (i : ℕ) : A := Gap.step τ^i * mi true n

def figure (n : MI) (i : ℕ) : ℤ:= normalOp n.1 n.2.1 n.2.2 i
lemma theta (n : MI) (m : ℕ) : stare (tilt n m stone)=(normal:ℂ)* (figure n m:ℂ) := by
  rw [tilt,mi]
  have he (a b c q p r): foot true a^p * foot true b^q * foot true c^r=foot true c^r * foot true b^q * foot true a^p := by
    have h (u v) (k m : ℕ): foot true u^k * foot true v^m=foot true v^m*foot true u^k:=(((balance true true u v).pow_left _).pow_right _).eq
    rw [h a b,mul_assoc,h a c,← mul_assoc,h b c]
  rw [he]; exact slope_pay ..

def eb (k : Axis) (u : MI × ℕ) := if h : k.val<3 then (bump ⟨k.val,h⟩ u.1,u.2) else (u.1,u.2+1)
lemma spins (n : MI) (i : ℕ) (k : Axis) : tilt n i * Gap.step k= tilt (eb k (n,i)).1 (eb k (n,i)).2 := by
  refine Fin.lastCases (i:=k) ?_ fun j=>?_
  · change _ * Gap.step τ= tilt n (i+1)
    have he : Gap.step τ * mi true n = mi true n * Gap.step τ := (foot_mi true true τ n).eq
    rw [tilt,tilt,pow_succ,mul_assoc,← he,mul_assoc]
  unfold eb; rw [dif_pos (show (Fin.castSucc j).val<3 from j.isLt)]; dsimp only
  rw [tilt,tilt,bump_mi,mul_assoc]; rfl

def census (u : MI) := u.1+u.2.1+u.2.2
def sgn (u : MI) : ℤ := (-1)^census u
lemma alike (q r : MI) : mi true q * mi true r = mi true (q+r) := by
  dsimp only [mi]
  simp only [Prod.fst_add,Prod.snd_add,pow_add];
  have he :∀ i j k m, Commute (foot true i^k) (foot true j^m) := fun i j k m=> ((balance true true i j).pow_left (k:ℕ)).pow_right (m:ℕ)
  -- explicit
  let X := foot true 0; let Y:= foot true 1; let V:= foot true 2
  change X^_*Y^_*V^_* (X^_*Y^_*V^_)= X^_*X^_* (Y^_*Y^_)*(V^_*V^_)
  let b:=Y^q.2.1; let c:=V^q.2.2; let d:=X^r.1; let e:=Y^r.2.1; let f:=V^r.2.2
  change _ * b * c * (d*e*f)= X^q.1*d*(b*e)*(c*f)
  simp only [mul_assoc]; rw [(he 2 0 q.2.2 r.1).left_comm] -- may need show
  have h : Commute b d := he ..; rw [h.left_comm]; have p : Commute c e:=he ..; rw [p.left_comm]

lemma less (u : MI) (p : SmoothGap) : mi false u p= (sgn u:ℂ) • mi true u p := by
  have h (i : Axis) (n : ℕ) (p) : (foot false i^n) p=((-1:ℂ)^n) • ((foot true i^n) p) := by
    induction n with
    | zero=>simp
    | succ n ih=>rw [power_age, power_age,ih,pow_succ,foot]; simp [foot]; exact (neg_smul ((-1:ℂ) ^ n) (((Gap.step i)) ((Gap.step i^n) p))).symm
  simp_rw [mi,Module.End.mul_apply,h,map_smul,smul_smul]
  push_cast [sgn,census]; rw [pow_add,pow_add,mul_assoc]
lemma two (p q : MI) (x) : mi false p (mi true q x)= (sgn p:ℂ) • tilt (p+q) 0 x := by
  rw [less, ← Module.End.mul_apply,alike, tilt,pow_zero,one_mul]

def get (v : List Axis) (p q : MI) := v.foldl (fun u k=>eb k u) (p+q,0)
def color (v : List Axis) (p q : MI) : ℤ := let u:= get v p q; sgn p * figure u.1 u.2
noncomputable def word : List Axis → A
  | []=>1
  | i::v=>Gap.step i * word v
lemma letters (v : List Axis) (s : MI × ℕ) : tilt s.1 s.2 * word v= tilt (v.foldl (fun u k=>eb k u) s).1 (v.foldl (fun u k=>eb k u) s).2 := by
  induction v generalizing s with
  | nil=>rw [word,mul_one]; rfl
  | cons i v h=>rw [word,← mul_assoc,spins,h]; rfl
lemma stint (v p q) : stare (mi false p (mi true q (word v stone)))=(normal:ℂ)*(color v p q:ℂ) := by
  have h:= letters v ((p+q),0)
  change tilt (p+q) 0 * word v=_ at h
  rw [two, map_smul, ← Module.End.mul_apply,h,theta]; unfold color get; simp only [Int.cast_mul,smul_eq_mul]; ring_nf

def boss (b : Bool) (i : Axis) (a c : Spin) := if b then Camera.K i a c else Camera.K i c a
def iform (b : Bool) (z t : FIndex) := Credit.sum <| [0,1,2,3].map fun i :Axis => ((Credit.zn (-16))*silver (boss b i t.1 z.1)) * zn (color [i] z.2 t.2)
lemma b_val (b i x y) : (boss b i x y).money=coeffCR b i x y := by cases b <;> simp [boss,coeffCR,Camera.kij]

/-- Pair just dropping the -i. `b` is type in x *after* flipping. -/
theorem f_view (b : Bool) (z t : FIndex) : stare (directed b (ket z) (ket t))=(normal:ℂ)*(iform b z t).money := by
  change stare (directed b (C z.1 z.2) (C t.1 t.2))=_
  simp_rw [psD,present,map_sum,map_smul,iform,Credit.sum_money]; rw [List.map_map]
  have h (p : Axis→ℂ) : ([0,1,2,3].map p).sum = ∑ i:Axis,p i := by simp [Fin.sum_univ_succ]
  rw [h, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; dsimp only [Function.comp_apply]; rw [Credit.times,zn_pay,Credit.times,cc,b_val,zn_pay]
  have he := stint [i] z.2 t.2; rw [word,word,mul_one] at he; rw [he]; push_cast; simp only [smul_eq_mul]; ring

lemma fineD {x : E4} (hx : x≠0) (i j : Axis) : eye x ((Gap.step i * Gap.step j) stone)=
    ((YM.Maxwell.grad i (YM.Maxwell.grad j Green) x:ℝ):ℂ) := by
  change (Gap.step i (Gap.step j stone)).val x=_; unfold stone; rw [light,light,lap _ _ hx]
lemma curlwork (a b k m : Axis) (f : Axis→Axis→SmoothGap) (pf : ∀ i j,f i j = word [i,j] stone) :
    curl a b k m= ((if k=b then f a m else 0)-(if m=b then f a k else 0))-
     ((if k=a then f b m else 0)-(if m=a then f b k else 0)) := by
  apply Gap.eyes; intro i p
  simp_rw [pf,word]; simp only [mul_one,map_sub]
  have he : eye i (curl a b k m)=((YM.Maxwell.bareCurl a b k m i:ℝ):ℂ) := lap _ (fun x z=>YM.Maxwell.Bare.curl_diff z a b k m) p
  rw [he,YM.Maxwell.bareCurl,Pi.sub_apply, YM.Maxwell.Bare.opp_grad p, YM.Maxwell.Bare.opp_grad p]
  split_ifs <;> simp only [fineD p, map_zero,Complex.ofReal_sub,Complex.ofReal_zero]

-- use first Coord truck per GIndex. need computable proxy (truck noncomp); use if

def gp (i : GIndex) : Axis×Axis := if i.1 then ((i.2.val.1+1).castSucc,(i.2.val.1+2).castSucc) else (τ,i.2.val.1.castSucc)
def cpic (a b k m : Axis) (p q : MI) : ℤ := (if k=b then color [a,m] p q else 0)-(if m=b then color [a,k] p q else 0) - ((if k=a then color [b,m] p q else 0) - (if m=a then color [b,k] p q else 0))
lemma ink (p q : MI) (a b k m) : stare (mi false p (mi true q (curl a b k m)))=(normal:ℂ)* (cpic a b k m p q:ℂ) := by
  rw [curlwork a b k m (fun i j=> word [i,j] stone) (fun i j=>rfl)]
  unfold cpic
  split_ifs <;> simp only [map_sub,map_zero, Int.cast_sub,Int.cast_zero, stint,mul_sub, mul_zero]

def gico (x y : GIndex) := zn (pay (!x.1) (cpic (gp x).1 (gp x).2 (gp y).1 (gp y).2 x.2.val.2 y.2.val.2))
theorem g_view (x y : GIndex) : stare (colored (slight (ket x)) (ket y))=(normal:ℂ)*(gico x y).money := by
  have h : colored (ket x) (ket y)= mi false x.2.val.2 (mi true y.2.val.2 (curl (gp x).1 (gp x).2 (gp y).1 (gp y).2)) := by
    rw [colored,on_ket]; dsimp only; rw [LinearMap.comp_apply,Solution.game,on_ket]; rfl
  rw [s_k,gico,zn_pay]; cases Bool.not x.1 <;> simp [h,ink]
end YM.GaugeFieldConstruction.Wick.Raster
