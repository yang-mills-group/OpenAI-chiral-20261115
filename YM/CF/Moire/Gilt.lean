import YM.CF.Moire.Alt
/-! Extensive *nonperturbative* analytically tilted Weyl sea. Projection complexification with gauge for sector extensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Moire
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire Branch Nacre
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m:ℕ}{n:Side}
variable {U:Type*}[NormedAddCommGroup U]
abbrev Sera(n:Side)(e:ℝ):= ↥(Openc (More n) e)
structure Had(b:ℝ)(e:ℝ)(F: Seal (Site (More n)))(P:Chin n→U):Prop where
 base (x:Sera n e): ‖P x.val‖≤ b
 high (x y:Sera n e): ‖P x.val-P y.val‖≤ b*((forum n e).eval F x y)
variable {b d e w r:ℝ}{S:Seal (Site (More n))}{P Q:Chin n→U}
lemma Had.spill(h:Had b e S P)(p:b≤r): Had r e S P:=⟨fun x=>(h.base x).trans p,fun x y=>(h.high x y).trans (mul_le_mul_of_nonneg_right p ((forum n e).pos ..))⟩
lemma Had.raise(h:Had b e S P)(l:0≤b){T:Seal (Site (More n))}(p:S⊆T): Had b e T P:=⟨h.base,fun x y=>(h.high x y).trans (mul_le_mul_of_nonneg_left ((forum n e).includeV p x y) l)⟩
lemma Had.mix(h:Had b e S P)(v:Had w e S Q): Had (b+w) e S (fun x=> P x+ Q x):=⟨fun x=>(norm_add_le ..).trans (add_le_add (h.base _) (v.base _)),fun x y=> by rw [add_sub_add_comm,add_mul]; exact (norm_add_le ..).trans (add_le_add (h.high ..) (v.high ..))⟩
lemma Had.downs(h:Had b e S P) :Had b e S (fun x=> -P x):=⟨fun x=>by rw [norm_neg]; exact h.base _,fun x y=> by rw [←neg_sub', norm_neg]; exact h.high ..⟩
lemma Had.sumT {I:Type*}[DecidableEq I](W:Finset I)(F:I→Chin n→U)(c:I→ℝ)(h:∀ i,Had (c i) e S (F i)): Had (∑ i∈W,c i) e S (fun x=> ∑ i∈W,F i x):=by
 induction W using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact ⟨by simp,by simp⟩
 | @insert i W hp ih=> simp only [sum_insert hp]; exact (h i).mix ih
lemma Had.tag [NormedSpace ℝ U] (h:Had b e S P)(c:ℝ): Had (‖c‖*b) e S (fun x=> c • P x):=⟨fun x=>by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (h.base _) (norm_nonneg _),fun x y=>by rw [←smul_sub,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.high ..) (norm_nonneg _)⟩
lemma Had.fin {β:Type*} [NormedSpace ℂ U][NormedAddCommGroup β][NormedSpace ℂ β] (h:Had b e S P)(L:U→L[ℂ] β): Had (‖L‖*b) e S (L ∘ P):=by
 refine ⟨fun x=> (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h.base _) (norm_nonneg _)),fun x y=>?_⟩; rw [comp_apply,comp_apply,←map_sub,mul_assoc]; exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h.high ..) (norm_nonneg _))
variable {J K: Chin n→ℂ}
lemma Had.forge(h:Had b e S J)(g:Had w e S K)(p:0≤b)(q:0≤w): Had (2*(b*w)) e S (fun x=> J x * K x):=by
 refine ⟨fun x=>?_,fun x y=>?_⟩
 · rw [norm_mul]; exact (mul_le_mul (h.base _) (g.base _) (norm_nonneg _) p).trans (le_mul_of_one_le_left (mul_nonneg p q) (by norm_num))
 let c:=(forum n e).eval S x y; have hv:0≤c:=(forum n e).pos ..
 rw [show J x.val*K x.val-J y.val*K y.val=(J x.val-J y.val)*K x.val+J y.val*(K x.val-K y.val) by ring]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; exact (add_le_add (mul_le_mul (h.high ..) (g.base _) (norm_nonneg _) (mul_nonneg p hv)) (mul_le_mul (h.base _) (g.high ..) (norm_nonneg _) p)).trans_eq (by ring)
lemma fealty (P : Cin→ℝ): P=P:=rfl
def titanic (e N:ℝ):= Real.exp (2*e*N)
lemma trailK (x:Site (More n))(w:Walk)(h:0<e)(N:ℝ)(H:(w.length:ℝ)≤N): Had (titanic e N) e (traceP x w) (fun V:Chin n=>track V x w) :=by
 let S:=traceP x w; let j:=w.length; have hu:(1+e)^j≤ Real.exp (e*j):=by
    rw [mul_comm e,Real.exp_nat_mul]; apply pow_le_pow_left₀ (by linarith); linarith [Real.add_one_le_exp e]
 let Z:= j*e; have he:titanic e (j:ℝ)=Real.exp (e*j)*Real.exp Z:=by unfold titanic Z; rw [←Real.exp_add]; congr 1; ring
 have hz: 0≤Z:=by unfold Z; positivity
 refine Had.spill (b:=titanic e (j:ℝ)) ?_ (by unfold titanic; gcongr)
 refine ⟨fun A=> (track_size e h.le x w A A.property).trans (hu.trans ?_),fun A B=>?_⟩
 · rw [he]; exact le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_exp hz)
 apply (track_vol e h.le x w _ _ A.property B.property).trans; change ↑j * ((1+e)^j *Tulip.fare S _ _) ≤ _* (Tulip.fare S _ _/|e|)
 let Y:=Tulip.fare S A.val B.val; have hy:0≤Y:=fare_t ..
 have hp: ↑j*((1+e)^j*Y)= (1+e)^j*Z*(Y/e):=by unfold Z; field_simp
 rw [hp,abs_of_pos h,he]; change _≤ _ * (Y/e); refine mul_le_mul_of_nonneg_right (mul_le_mul hu ?_ hz (Real.exp_pos ..|>.le)) (by positivity); linarith [Real.add_one_le_exp Z]
lemma whirl_T (x:Site (More n))(w:Walk)(h:0<e)(N:ℝ)(H:(w.length:ℝ)≤N): Had (titanic e N) e (traceP x w∪traceP x (reverse w)) (whirl x w):=by
 let S:= traceP x w∪traceP x (reverse w); let y:=titanic e N
 let L:=ContinuousLinearMap.snd ℂ (Op Slot) (Op SU.F); have hp: ‖L‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun k=>by rw [one_mul]; exact le_max_right ..)
 have he(w':Walk)(H':w'.length=w.length)(g: traceP x w'⊆ S): Had y e S (fun z=> (track z x w').2):= ((Had.raise (trailK x w' h N (by rwa [H'])) (Real.exp_pos ..|>.le) g).fin L).spill (mul_le_of_le_one_left (Real.exp_pos ..|>.le) hp)
 have hf:= ((he w rfl subset_union_left).mix (he (reverse w) (by simp [reverse]) subset_union_right).downs).tag (1/2:ℝ); unfold whirl; simp_rw [sub_eq_add_neg]; apply hf.spill; norm_num; linarith
end YM.CF.Moire
