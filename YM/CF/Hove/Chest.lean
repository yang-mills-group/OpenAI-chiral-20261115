import YM.CF.Hove.Bird
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable (j:ℕ)(p:4≤j)(e:Even j)
variable {c f:Side}(G:Ratio c f)(w:Odd G.count.val)(M:Male)(b:Bool)(o: Site c)(T:Script Male)(u:Use j G.count T)
variable {n:ℕ}
local notation "B"=> baseF b
local notation "W"=> wingF j G w T M b (heel G o)
variable (C:ℝ)(d:List Axis)
def Demark : Prop:=∀{c f:Side}(G:Ratio c f)(w:Odd G.count.val)(M:Male)(o:Site c)(T: Script Male),Use j G.count @T →∀ n:ℕ, 2*n<c.val→
 ∀ F:Cover→Pal,(∀ i k:Kt,∀ x:Cover,‖F x i k‖≤ m_fee b*tweight 1 x)→ let Wa:= wingF j G w T M b (heel G o) d * view_M o F; let L:=lace d.length G.count; ‖Wa‖≤ C*L ∧ ‖Wa-idealS j G M b d F‖≤ C*L/(1+(n:ℝ)) -- notation W conflicts tune
include e p
lemma deem (ad:d.length≤1) : ∃ C:ℝ,0≤C∧Demark j b C d:=by
 obtain ⟨R,z,h⟩:= lipV j b d (by omega) (by omega); let C:=2*(Haro.ξP * (Fintype.card Kt * (m_fee b*R)))
 have hc:0≤C:=by unfold C Haro.ξP; have ht:=mpe b; positivity
 refine ⟨C,hc,fun {c f} G w M o T u n v F H=>?_ ⟩
 let W':= wingF j G w T M b (heel G o) d * view_M o F; let L:=lace d.length G.count; have hl:0<L:=by unfold L lace; positivity
 obtain ⟨i,j⟩:=stamp_P j e G w M b o T u d (by omega) F _ _ (mpe b) H (fun i j=>h G w M i j) v
 refine ⟨i.trans ?_,j.trans_eq ?_⟩
 · unfold C; calc
     _ = (C/2)*L:=by unfold C L; ring
     _ ≤ C*L:=mul_le_mul_of_nonneg_right (by linarith) hl.le
 unfold C; ring -- tune
omit e p
lemma Demark.over {C':ℝ}(s:Demark j b C d)(z:C≤C'):Demark j b C' d:=by
 intro c f G w M o T u n v F H; obtain ⟨t,p⟩:=s G w M o @T u n v F H; have hp:0 ≤lace d.length G.count:=by unfold lace; positivity
 exact ⟨t.trans (mul_le_mul_of_nonneg_right z hp),p.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right z hp) (by positivity))⟩
abbrev φv (L:Side)(i:Axis)(s:Axis):Pal:= if i=s then (lace 1 L:ℂ) • baseF b else 0
local notation "H"=> rampF b o
structure BenchQ (A:ℝ)(N:ℕ): Prop where
 mass: ‖wingF j G w T M b (heel G o) []*rampF b o‖≤ A*lace 0 G.count
 nextV(s:Axis): ‖W [] *spanH b o s‖≤ A*lace 0 G.count
 scale: ‖W [] *rampF b o-(lace 0 G.count:ℂ) • baseF b‖≤ A*lace 0 G.count/(1+(N:ℝ))
 cap(i:Axis): ‖W [i] *rampF b o‖≤ A*lace 1 G.count/(1+(N:ℝ))
 turn(i s:Axis) : ‖W [i]*spanH b o s -φv b G.count i s‖≤ A*lace 1 G.count/(1+(N:ℝ))
 tube(i s:Axis): ‖W [i]*spanH b o s‖≤ A*lace 1 G.count
include p e
lemma hall_Q : ∃ C:ℝ,0 ≤ C∧∀ {c f:Side}(G:Ratio c f)(w:Odd G.count.val)(M:Male)(b:Bool)(o:Site c)(T:Script Male), Use j G.count @T→∀ n:ℕ, 2*n<c.val→ BenchQ j G w M b o T C n :=by
 choose P i L using fun x: Bool×Option Axis=> deem j p e x.1 x.2.toList (by cases hy:x.2<;>simp)
 let C:=∑ x,P x
 have hx(x):P x ≤ C:= single_le_sum (fun i' _=>i i') (mem_univ _)
 refine ⟨C,sum_nonneg fun _ _=> i _,fun {c f} G w M b o T u n v=>?_⟩
 have ht(x:Bool × Option Axis):Demark j x.1 C x.2.toList:=Demark.over _ _ _ _ (L x) (hx x)
 let Y(b:Option Axis): List Axis:= b.toList; have he:= ht (b,none) G w M o @T u n v
 have he'(a:Axis):= ht (b,some a) G w M o @T u n v
 have hl(i k:Kt)(x:Cover):‖baseF b i k‖≤ m_fee b *tweight 1 x:=(mp_iv ..).trans (le_mul_of_one_le_right (mpe b) (tw_one ..))
 have hz(a:Axis)(i k:Kt)(x:Cover): ‖moonB b a x i k‖≤ m_fee b * tweight 1 x:= (mon_v ..).trans_eq (by rw [mul_comm]; simp [tweight])
 let B₀:= baseF b; let F:= rampF b o
 have hh₀: F=view_M o (fun _=>B₀):=rfl
 obtain ⟨hvZ,r⟩:=he (fun _=>baseF b) hl; let S(i:List Axis)(f: Cover→Pal):= idealS j G M b i f
 refine ⟨hvZ,fun s=>(he (moonB b s) (hz s)).1,?_,?_,?_,fun i s=>(he' i (moonB b s) (hz s)).1⟩
 · apply le_trans _ r; rw [show (lace 0 G.count:ℂ) • baseF b=S [] (fun _=>B₀) from ?_ ]; swap; · unfold S B₀; rw [(sun_v j p G w M b _ 0).1,φ_sq]
   exact le_rfl
 · intro x; have he:=(he' x (fun _=> B₀) hl).2; apply le_trans _ he; change _ ≤ ‖wingF j G w T M b (heel G o) [x]*F-S [x] (fun _=>B₀)‖; rw [show S [x] (fun _=>B₀)=0 from (sun_v j p G w M b B₀ x).2, sub_zero]
 · intro a s; rw [←show idealS j G M b [a] (moonB b s)=φv b G.count a s from vita_q j p G w M b a s]; exact (he' a (moonB b s) (hz s)).2
end YM.CF.Hove
