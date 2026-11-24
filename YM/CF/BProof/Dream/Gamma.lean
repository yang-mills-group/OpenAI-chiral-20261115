import YM.CF.BProof.Dream.Kings
/-! Path (B-Gz) in symmetric unitary colour sector. `Q` over one Sheet reused in all 3 copies. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix SU Finset Function Metric Complex Extension.Mar Mag
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Kronecker ContDiff ComplexConjugate
attribute [local instance] opCStarAlgebra
variable {n : Type*}[Fintype n][DecidableEq n]
lemma lk:inK living:=⟨shiftB_U 1,shiftB_D 1⟩
lemma lv: livingᵀ=living:= shiftB_T 1
lemma forU (V:E) : inK (fund V):=⟨fund_U _,fund_det _⟩
def species (V:E): Op Sheet:= each (fund V)
lemma classK (V:E) : inK (species V):=⟨each_mem _, each_det _⟩
abbrev locus (i:Fin 5):= (center i)⁻¹
def nodeB (i:Fin 5): Op Sheet := mold (species (locus i)) living
lemma nodeT (i:Fin 5):(nodeB i)ᵀ=nodeB i:= moldT lv
@[simp] lemma speciesOne:species 1=1:= each_one
@[simp] lemma node0:nodeB 0=living:=by simp [nodeB,locus]
lemma moldS {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]{F G:X→Op n}(h: ContDiff ℝ ∞ F) (g: ContDiff ℝ ∞ G): ContDiff ℝ ∞ (fun x=> mold (F x) (G x)):=by
 let L:Op n→ₗ[ℝ] Op n:= ⟨⟨Matrix.transpose,transpose_add⟩,fun r X=>Matrix.transpose_smul r X⟩; exact (h.mul g).mul (L.toContinuousLinearMap.contDiff.comp h)
structure Gamma (i: Fin 5) where
 U: UNI Sheet
 a: Sheet→ℝ
 phases : ∀ j,MainT (a j)
 total : ∑ j,a j=0
 matchQ : nodeB i*star living=clockM U a 1
 stationary : i=0 → a=0
namespace Gamma
variable {i:Fin 5}(G:Gamma i)
def line := clockM G.U G.a
def seat (t:ℝ):= G.line t * living
@[simp] lemma line0: G.line 0=1:=by simp [line]
lemma road (t:ℝ) : inK (G.line t):=⟨clockU ..,(by rw [line,clocksDet,G.total,zero_mul,rose_zero])⟩
protected lemma smooth : ContDiff ℝ ∞ G.line:=clockS ..
@[simp] lemma seat0 : G.seat 0=living:=by simp [seat]
lemma seat1 : G.seat 1=nodeB i:=by rw [seat,line,← G.matchQ,mul_assoc,lk.1.1,mul_one]
lemma share (t:ℝ): G.line t*living=living*(G.line t)ᵀ:=by
 apply clockShares G.U G.a _ G.phases; have he:= G.seat1; unfold seat line at he; rw [he]; exact (nodeT _).symm.trans (by rw [← he,transpose_mul,lv]) -- tune dependent he
lemma seatLift (t:ℝ): G.seat t=mold (G.line (t/2)) living :=by
 let V:=G.line (t/2); have he:V*V=G.line t:=by unfold V line; rw [clocks,show t/2+t/2=t from by ring]
 unfold mold seat; change _=V*living*Vᵀ; rw [mul_assoc,← show V*living=living*Vᵀ from G.share _,← mul_assoc,he] -- share pattern V def
lemma sound (t:ℝ) : (G.seat t)ᵀ=G.seat t ∧ inK (G.seat t):=by rw [G.seatLift t]; exact ⟨moldT lv,moldK (G.road _) lk⟩
lemma seat_s : ContDiff ℝ ∞ G.seat:= G.smooth.mul contDiff_const
lemma trivial (G:Gamma 0)(t:ℝ): G.line t=1:=by simp only [line,G.stationary rfl,clockM,Pi.zero_apply,zero_mul,rose_zero]; exact dial_one _
lemma stays (G:Gamma 0)(t:ℝ): G.seat t=living:=by rw [seat,G.trivial,one_mul]
lemma rad : ∃ (M:Op Sheet)(r:ℝ),0<r ∧ r<1∧∀ t∈Zone, ‖G.seat t-M‖≤r:=by
 obtain ⟨Q,r,p,h,W⟩:= clockDisk _ _ G.phases; refine ⟨Q*living,r,p,h,fun t hx=>?_⟩; rw [seat, ← sub_mul, show living=(⟨living,lk.1⟩:UNI Sheet).val from rfl,CStarRing.norm_mul_coe_unitary]; exact W _ hx.1 hx.2
lemma existsG (i:Fin 5): Nonempty (Gamma i):=by
 by_cases h:i=0
 · subst i; refine ⟨⟨1,0,fun _=>main0,(by simp),?_,fun _=>rfl⟩⟩; simp only [node0,lk.1.2,clockM,Pi.zero_apply,zero_mul,rose_zero]; exact (dial_one _).symm
 obtain ⟨U,d,he,v,w⟩:= centreS i; change nodeB _ * star living=_ at he; refine ⟨⟨U,d,v,w,?_,fun u=>(h u).elim⟩⟩; rw [clockM,he]; simp only [Function.comp_def,mul_one]
end Gamma
def gamma (i:Fin 5) : Gamma i:=Classical.choice (Gamma.existsG i)
end YM.CF.BProof.Dream
