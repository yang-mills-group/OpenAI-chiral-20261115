import YM.CF.Laic.Potion
import YM.Planned.STATIONARY_JET_PORT.Pack
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n c m:Side}{ι κ:Type}[Fintype ι][Fintype κ][LinearOrder κ]{k:ℕ}{l:ι→Site n}{u:κ→Site n}{x:Positions ι}{a b d:ℝ}
lemma inkC{F:Positions ι→ Op κ}(p:smooth F x)(h:CableM l u u a k F x b)(t:0<a)(hv:0≤b):CableM l u u (slip k a) k (fun y=>star (F y)) x b:=by
 intro r; let X:=coinZ r ∘ F; have he: bornMatrix (fun y=>Matrix.transpose (X y)) x:=fun i j=> inkJet r p j i; have ht:= Cable.switch t hv (h r)
 cases r with
 | false=> change Cable l u u none _ k (fun x=>coinZ false (star (F x))) x _; rw [show (fun x=>coinZ false (star (F x)))=(fun x=>-(coinZ false (F x)).transpose) from funext fun x=>Matrix.ext fun i j=> rfl]; exact ht.neg he
 | true=> exact ht
variable {L: Side}
-- small row spin twist uses block diagonal evaluation. analytic comp linear Beacon: formula
lemma linearN{B C:Type}[NormedAddCommGroup B][NormedSpace ℝ B][NormedAddCommGroup C][NormedSpace ℝ C]{F:Positions ι→B}{u:Site n}(L:B→L[ℝ]C)(p:ContDiffAt ℝ ω F x)(h:Beacon l a k F u x b)(q:‖L‖≤ d): Beacon l a k (L ∘ F) u x (d*b):=by
 intro i e r; unfold Push.Uniform.entry; rw [L.iteratedFDeriv_comp_left p le_top]; change ‖L (Push.Uniform.entry F x r)‖ ≤ _; refine (L.le_opNorm _).trans ?_; rw [mul_assoc]; exact mul_le_mul q (h _ e _) (norm_nonneg _) ((norm_nonneg _).trans q)
lemma matrix_w {κ:Type}[Fintype κ][DecidableEq κ]{F:Positions ι→ Op κ}{u:Site n}(p:smooth F x)(h:∀ i j,Beacon l a k (fun y=>F y i j) u x b)(e:0≤b): Beacon l a k F u x (‖(coordL (k:=κ)).symm.toContinuousLinearMap‖*b):=by
  let T(y):κ→κ→ℂ:=fun i j=>F y i j; let L:=coordL (k:=κ); let U:= L.symm.toContinuousLinearMap; have hv: ContDiffAt ℝ ω T x:=contDiffAt_pi.mpr fun i=> contDiffAt_pi.mpr fun j=>p i j
  have hh:Beacon l a k T u x b:=by
     intro i ht q; apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro j; refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun r=>?_; let l:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:κ=>ℂ) r).comp (ContinuousLinearMap.proj (φ:=fun _:κ=> κ→ℂ) (R:=ℝ) j); have he: entry (l ∘ T) x q = l (Push.Uniform.entry T x q):=by unfold Push.Uniform.entry; rw [l.iteratedFDeriv_comp_left hv le_top]; rfl
     rw [show entry T x q j r=_ from he.symm]; exact h j r i ht q
  exact linearN U hv hh le_rfl
abbrev glyphP (P:Side)(x:Site P)(i:SpinIdx×Slot): Single P:= ((x,i.1),i.2)
abbrev lect (x:Site c)(i j: Site c):ℕ:=0 -- remove
abbrev stepB (x y: Site c)(F:Op (Single c)):Op (SpinIdx × Slot):=Matrix.of fun i j=> F (glyphP c x i) (glyphP c y j)
private lemma fore(a:Shape)(x y:Site c)(F:Op (Single c)): stepB x y (ape c a F)=(milU a (spinX a.s) inert x).val*stepB (a.mills c x) (a.mills c y) F*star (milU a (spinX a.s) inert y).val:=by
 obtain ⟨B,rfl⟩:= (love c).surjective F
 let V:= spinX a.s; have he:= wingX a V inert B -- params
 change stepB x y (sings false (prepU a V inert c) (love c B))= _; rw [he]; exact tap_sg false B (Tofu a c) (fun i=> milU a V inert i) x y
private def Mtx (k:SpinIdx×Slot)(j:SpinIdx×Slot)(A B:UNI (SpinIdx×Slot)): Op (SpinIdx×Slot)→L[ℝ]ℂ:= (show Op _→ₗ[ℝ]ℂ from {
 toFun:=fun X=> (A.val*X*star B.val) k j
 map_add' := fun x y=>by rw [mul_add,add_mul]; rfl
 map_smul':=fun a x=> by rw [Matrix.mul_smul,Matrix.smul_mul]; rfl }).toContinuousLinearMap
private lemma Mtx_one (k j:SpinIdx×Slot)(A B): ‖Mtx k j A B‖ ≤ 1 := by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; change ‖(A.val*x*star B.val) k j‖≤ _; apply (norm_entry ..).trans; rw [one_mul, ← show ((B⁻¹).val: Op _)=star B.val from rfl,CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
def insD:ℝ:= 1+2*‖(coordL (k:=SpinIdx×Slot)).symm.toContinuousLinearMap‖
lemma billW {l:ι→Site n}{u:Site (More c)→Site n}{F:Positions ι→ Op (Single c)}(p:smooth F x)(i:Signed)(h:CableM l (u∘ (incX i⁻¹).anon c ∘place_x) (u∘(incX i⁻¹).anon c∘place_x) a k F x b) (hc:0≤b)(v:0<a): CableM l (u∘place_x) (u∘place_x) (slip k a) k (fun y=>ZoneH (incX i) (F y)) x (insD*b):=by
 let P:=incX i; let X:=ape c P ∘ F; have hh(j:Site c): (incX i⁻¹).anon c (node (P.mills c j))=node j:=by
    rw [Shape.nodex]; let v:=node j; obtain ⟨V,hv⟩:∃ V', wrap (More c) V'=node j:= ⟨natural v,nat_true _⟩; rw [←hv,Shape.anno,Shape.anno,←Nacre.palm]; unfold P; rw [wink,inv_mul_cancel]; simp [Shape.motion,incX]
 let T:=(twist (prepU P (spinX i) inert c)).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
 have ht : ContDiffAt ℝ ω X x:= T.contDiff.contDiffAt.comp x (Nacre.tort.mpr p)
 have hm: 0 < insD:=by unfold insD; positivity
 have hv: CableM l (u ∘ place_x) (u ∘place_x) a k X x (insD*b):=by
    refine ledger (Nacre.tort.mp ht) ?_; rintro ⟨⟨v,s⟩,f⟩ ⟨⟨w,t⟩,j⟩
    let Z(y):= stepB (P.mills c v) (P.mills c w) (F y); let D:=Decay a (u (node v)) (u (node w)); let K:=2*b*D; have hz :0 ≤ D:=decay_pos ..|>.le; have hx(s f):Beacon l a k (fun z=> Z z s f) (u (node v)) x K:=by
       have he:= pendant p h (glyphP c (P.mills c v) s) (glyphP c (P.mills c w) f); unfold Function.comp place_x at he; change Beacon _ _ _ _ (u ((incX i⁻¹).anon c (node _))) _ (_ * Decay a (u ((incX i⁻¹).anon c (node _))) (u ((incX i⁻¹).anon c (node _)))) at he; dsimp only [glyphP] at he; rw [hh,hh] at he; exact he
    have he : smooth Z x:=fun i j=>p _ _; have hh:=matrix_w he hx (by positivity)
    let A:= Mtx (s,f) (t,j) (milU P (spinX P.s) inert v) (milU P (spinX P.s) inert w); have hT(z): X z ((v,s),f) ((w,t),j)=A (Z z):=Matrix.ext_iff.mpr (fore P v w (F z)) (s,f) (t,j)
    simp_rw [hT]; refine (linearN A (Nacre.tort.mpr he) hh (Mtx_one ..)).mono ?_; let A':=(coordL (k:=SpinIdx×Slot)).symm.toContinuousLinearMap; unfold insD K; change (1:ℝ)* (‖A'‖*(2*b*D))≤ (1+2*‖A'‖)*b *D; nlinarith [mul_nonneg hc hz]
 simp_rw [zone_c]; unfold Thera.jazz; split
 · let B:= fun y=>star (X y); have he: smooth B x:= Nacre.tort.mp ((starL ℝ: Op (Single c) ≃L[ℝ] Op (Single c)).contDiff.contDiffAt.comp x ht); exact inkN he (inkC (Nacre.tort.mp ht) hv v (mul_nonneg hm.le hc))
 exact hv.mild (slip_le k v.le) (mul_nonneg hm.le hc)
end YM.CF.Laic
