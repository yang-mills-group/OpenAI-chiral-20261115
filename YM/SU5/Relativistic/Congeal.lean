import YM.SU5.Relativistic.Rust
/-! # Lifting costs to one actual sensor. Vectors with AP seam signs. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Cube Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Lat Fock Nacre Skye Scroll Rush Dial Tulip Pannier.Chancel UpStart Buffered
open Lifted (nodeC basisC node_of)
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra screen_fin
local notation "I"=>Complex.I
local notation "φ"=> 2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
variable {d:ℕ}{s:Finset ℤ}{c:ℤ→Behind→ℂ}{a r:ℝ} (P:UpStart d s c r (2*a))
variable (n:Side)(M:Jill.Male)
local notation "Q"=> spar 4 M (1:Pane n)
-- height & labels summed, relative to anchor arbitrary so all financable & AP seam

def flowE (u:Site n) : Behind:=fun i=> pm u i.castSucc
def flowL (u:Site n):ℝ:= pm u TA
lemma flow_meet (u:Site n):pm u=tack (flowE n u) (flowL n u):=by
 funext i; induction i using Fin.lastCases <;> simp only [tack,Fin.lastCases_last,Fin.lastCases_castSucc] <;> rfl
lemma here_s(u:Site n):flowE n u∈ backPane ∧ flowL n u∈Φ:=by
 exact ⟨(afloat _).2 fun i=>Set.Ioc_subset_Icc_self (pm_zone u i.castSucc), Set.Ioc_subset_Icc_self (pm_zone u TA)⟩
lemma fibre_base (x: Cover)(k:Site n)(i b:SpinIdx)(f g:SU.Slot): (acts (star (ear n).val) (basisC n x i f)).ofLp ((k,b),g)= if i=b∧f=g then (normF n)⁻¹* mode (mel k) (-x) else 0:=by
 rw [basisC,map_smul,WithLp.ofLp_smul,Pi.smul_apply,over_basis, Lifted.index]; simp only [smul_eq_mul]; split
 · rw [mul_div_assoc', ← windWave]; ring -- parentheses tune
 rw [mul_zero]

def gust(n:Side)(o:Cover)(i:SpinIdx)(n':ℤ)(f:WalkA→₀ℂ)(s:SU.Slot): Ket (Single n):= f.sum fun x z=> z • basisC n (o+tack x n') i s
def strum(n:Side)(o:Cover)(T:ℕ)(F:Waxy)(s:SU.Slot): Ket (Single n):= ∑ i:SpinIdx, ∑ k∈ TwistT T,gust n o i k (F i k) s
def snap (n:Side)(o:Cover)(T:ℕ)(F:Waxy)(u:Site n):= mode (mel u) (-o) • timbre T F (flowE n u) (flowL n u)
lemma gust_kernel (o: Cover)(A b:SpinIdx)(i:ℤ)(F:WalkA→₀ℂ)(f g:SU.Slot)(k:Site n) : (acts (star (ear n).val) (gust n o A i F f)).ofLp ((k,b),g)= if A=b ∧ f=g then (normF n)⁻¹*(mode (mel k) (-o))*array F (flowE n k)*soundT i (flowL n k) else 0:=by
 unfold gust; simp only [map_sum,map_smul,Finsupp.sum, WithLp.ofLp_sum,Finset.sum_apply, WithLp.ofLp_smul,Pi.smul_apply, smul_eq_mul,fibre_base]
 split_ifs with h; swap; · simp [h]
 rw [Finset.mul_sum,Finset.sum_mul]; refine sum_congr rfl fun u p=>?_; rw [neg_add,mode_shift,mel,flow_meet,tagF]; ring
lemma wake_kernel (o:Cover)(T:ℕ)(F:Waxy)(f:SU.Slot): acts (star (ear n).val) (strum n o T F f)=shellV n f (snap n o T F):=by
 apply PiLp.ext; rintro ⟨⟨k,b⟩,g⟩; unfold strum; simp_rw [map_sum,WithLp.ofLp_sum,Finset.sum_apply,gust_kernel]; unfold shellV; by_cases p:g=f; swap; · simp [p,Ne.symm p]
 subst g; rw [Finset.sum_eq_single b]
 · change (∑ i∈TwistT T,_)=(if _ then _ else _); simp only [and_self,↓reduceIte]; unfold snap timbre; rw [WithLp.ofLp_smul,Pi.smul_apply]; change _=(normF n)⁻¹*(mode _ _*boardZ T F _ _ _); unfold boardZ; simp_rw [Finset.mul_sum]; exact sum_congr rfl fun x _=>by ring
 · intro i _ p; simp [p]
 simp

lemma freezeSpin(f:Site n → Ket SpinIdx)(o:Cover)(i:Site n):‖mode (mel i) (-o) • f i‖=‖f i‖:=by rw [norm_smul,mode_real _ _ (mel_h i).1,one_mul]
local notation "F" n o=> strum n o
include P
lemma take_patch {C:ℝ}(t:0 < C)(A:ℕ)(R:Waxy) (h:∀ k∈backPane,∀ u∈Φ, ‖timbre A R k u-target s c k u‖≤C):
    ∀ᶠ N:ℕ in atTop,∀ (M:Jill.Male),N≤ M.val.val → ∀ n:Side,∀ (f:SU.Slot)(o:Cover), let X:=strum n o A R f; ‖acts (spar 4 M (1:Pane n)) X-X‖≤3*C:=by
 obtain ⟨N,w⟩:= P.critical _ t; filter_upwards [eventually_ge_atTop N] with D v M hm n f o X
 rw [←act_unit_norm (star (ear n))]; change ‖acts (star (ear n).val) _‖≤ _; rw [prime_fourier n M,map_sub, twist_formula, act_mul,act_mul,show acts (star (ear n).val) X= _ from (show _=shellV n f (snap n o A R) from wake_kernel n o A R f)] -- ordering `act_mul` goes star outer? after map_sub
 let H:= snap n o A R
 rw [act_unit,shell_bands,shell_sub]
 let g:= (fun i=>acts (bar 4 M.val (mel i)) (H i))
 apply shellBound _ f _ (by positivity); intro i
 let S:= bar 4 M.val (mel i); have he: S= UpStart.mana M (flowE n i) (flowL n i):= by unfold S mel mana; rw [flow_meet]
 have ht := here_s n i; let U:=timbre A R (flowE n i) (flowL n i); let Y:=target s c (flowE n i) (flowL n i)
 have hb:‖acts S Y-Y‖ ≤ C := he.symm ▸ w M (v.trans hm) (flowE n i) ht.1 (flowL n i) ht.2
 have hu: ‖U-Y‖≤C:=h (flowE n i) ht.1 (flowL n i) ht.2
 have hw:‖acts S U -acts S Y‖ ≤ C:=by rw [←map_sub]; exact (((acts S).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (he.symm ▸ spiritShrink _ _ ht.1 ht.2 M))).trans hu
 change ‖acts S (mode (mel i) (-o) • U)-mode (mel i) (-o) • U‖≤ _; rw [map_smul,←smul_sub,norm_smul,mode_real _ _ (mel_h i).1,one_mul]
 rw [norm_sub_rev U Y] at hu
 linarith only [hu,hb,hw,norm_sub_le_norm_sub_add_norm_sub (acts S U) (acts S Y) Y,norm_sub_le_norm_sub_add_norm_sub (acts S U) Y U]
end YM.CF.Crest.Sleet
