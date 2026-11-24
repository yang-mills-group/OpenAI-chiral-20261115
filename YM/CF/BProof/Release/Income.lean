import YM.CF.BProof.Release.Sky

/- v normalized product. Pointwise release normal formula. `income` exact if fares & chunk.
`inflate` tax brings normal weights OUT of gaussian; subsequently work cancels them.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Release.Sky
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Locale hot Law
open scoped Topology BigOperators Classical ENNReal Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
variable (K:Chart G)(P: Pub G)
variable {s:Side}(Y:Yard s)(T:PathData G){c:Clip}{M:ℕ}(θ κ:ℝ)(y:ℝ){R q w:ℝ}(X:Beam c R Y.short M y) (H:Room Y M)(u:T.Bounds c w R q)(h: θ∈Set.Icc (1/2) 2)
variable (a:Book K P Y κ X)(Z:Finset Y.Col)(b:Y.Col)(x:Plan Y)(W:House Y)

def σ := P.base Y.Apt (g y)*Day.Z (trunc y) (Roll.Place Y)
def light := P.dust (g y) (pin Y T θ X Z x b)
def inflate := Day.ar (hot.entry Y x b)/2
def watch := ∑ b∈Zᶜ, (light P Y T θ y X Z b x+inflate Y b x)
def scale := σ P Y y ^ (Zᶜ.card) * Real.exp (watch P Y T θ y X Z x)
abbrev full := ∏ i,Day.ticket (trunc y) (hot.entry Y x i)
variable {Z x}
variable (v:bed Y κ y (Sky.reach Y T θ y X Z W x)=Z) (p:Fares Y y x)
lemma σ_pos : 0<σ P Y y:= mul_pos (P.base_pos _ _ (coin_pos ..)) (Day.filled _ _ (trunc_pos _)) -- tune
lemma open_o (q:b∉Z) : Sky.reach Y T θ y X Z W x b= Pub.stamp (g y) (Locale.A Y y b) (pin Y T θ X Z x b) := if_neg q
include v p a H h u
lemma windows (q:b∉Z): hot.doors P Y T θ κ X Z x b:=by
 apply (Pub.vault_v P _ _ _ _ (fun i=> hot.admitted K P Y T θ κ X H u h Z x a p b i)).mpr; rw [← open_o Y T θ y X b W q]; exact Locale.dry_s _ _ _ _ _ v q
omit v p
lemma incoming (p:bill P Y κ y Z (Beam.drive T θ X Z x)≠0): Fares Y y x:=by
 have hx(i:Y.Col): fee P Y κ y Z i (pin Y T θ X Z x i)≠0:= fun H=> p (prod_eq_zero (mem_univ i) H)
 intro i; by_cases k:i∈ Z
 · specialize hx i; unfold fee at hx; rw [if_pos k, stable Y T θ X H u h Z x i k] at hx; exact Classical.byContradiction fun p=> hx (Day.ticket_off _ _ p)
 apply hot.reverse K P Y T θ κ X H u h Z x a (b:=i) _ k; intro b p; apply (Pub.ticket_v P _ _ _ (coin_pos ..)).mp; specialize hx b; unfold fee at hx; rw [if_neg p] at hx; exact hx
include v p
lemma fee_S : fee P Y κ y Z b (pin Y T θ X Z x b)= Day.ticket (trunc y) (hot.entry Y x b) * if b∈Z then 1 else σ P Y y*Real.exp (light P Y T θ y X Z b x + inflate Y b x) :=by
 unfold fee; split_ifs with q; rw [stable Y T θ X H u h Z x b q,mul_one]; rw [P.ticket_c _ _ _ _ (coin_pos ..) (windows K P Y T θ κ y X H u h a b W v p q)]
 let N:=Day.Z (trunc y) (Roll.Place Y); let t:=hot.entry Y x b; let l:= P.base Y.Apt (g y); let d:= light P Y T θ y X Z b x; let f:=inflate Y b x
 have hy:0<N:= Day.filled _ _ (trunc_pos _); have he:Day.ticket (trunc y) t=N⁻¹*Real.exp (-f):=by rw [Day.ticket,Day.ore,Set.indicator_of_mem (p b)]; unfold N Day.gar f inflate; ring_nf -- tune
 change l*Real.exp d=Day.ticket _ t *_; rw [he]; change _= _*(l*N*Real.exp (d+f)); rw [Real.exp_add,Real.exp_neg]; field_simp
lemma coinage : bill P Y κ y Z (Beam.drive T θ X Z x)= scale P Y T θ y X Z x*full Y y x:=by
 unfold bill full
 let Q(i:Y.Col):=fee P Y κ y Z i (pin Y T θ X Z x i); let V(i:Y.Col):=Day.ticket (trunc y) (hot.entry Y x i); let t(i:Y.Col):= light P Y T θ y X Z i x+inflate Y i x; let d:=σ P Y y; let g(i:Y.Col):= if i∈Z then (1:ℝ) else d*Real.exp (t i); have hp:Q=fun i=>V i*g i:=funext fun i=> fee_S K P Y T θ κ y X H u h a i W v p
 change (∏ i,Q i)=_*(∏ i,V i); rw [hp,prod_mul_distrib, mul_comm (∏ i,V i), ← prod_mul_prod_compl Z g, prod_eq_one (f:=g) (fun i hi=> if_pos hi),one_mul]; congr 1; unfold scale watch; rw [show (∏ i∈ Zᶜ,g i)=∏ i∈ Zᶜ,d*Real.exp (t i) from prod_congr rfl fun i hi=> if_neg (mem_compl.mp hi), prod_mul_distrib,prod_const, ←Real.exp_sum] -- tune
omit p v
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F][MeasurableSpace F][BorelSpace F][SecondCountableTopology F][CompleteSpace F]
-- normalization works for any chunky test. Fares included later in playback to ensure support automatically. Keep costs Borel global.
omit H h u a
@[fun_prop] lemma reach_m : Measurable (Function.uncurry (reach Y T θ y X Z)):= by
 unfold reach Function.uncurry wing; apply (stop_m Y y Z).comp (f:=fun (p:House Y × Plan Y)=> (p.1,fun b=> hot.entry Y (Beam.drive T θ X Z p.2) b)); apply measurable_fst.prodMk; let Q:=Beam.ζ T θ X Z; change Measurable (fun p:House Y × Plan Y=> MeasurableEquiv.curry _ _ ℝ ((Q.mulVecLin) p.2)); fun_prop
@[fun_prop] lemma watch_m : Measurable (watch P Y T θ y X Z) := by
 apply Finset.measurable_sum; intro i hi; apply Measurable.add; let Q:=Beam.ζ T θ X Z; change Measurable (fun x:Plan Y=>P.dust (g y) (Function.curry ((Q.mulVecLin) x) i)); apply (Pub.dust_m P (g y)).comp; unfold Function.curry; fun_prop; unfold inflate hot.entry Function.curry; fun_prop -- tune
include H h u a
lemma fund (f:House Y→ F)(p:Envelope f)(Z:Finset Y.Col): (∫ x,chunk Y κ y Z f x ∂lobby Y) = ∫ v, (Beam.ζ T θ X Z).det • (∫ w:hot.Field Y,scale P Y T θ y X Z (Function.uncurry w) • chunk Y κ y Z f (reach Y T θ y X Z v (Function.uncurry w)) ∂Measure.pi fun _:Y.Col=> Day.mark (trunc y) (Roll.Place Y)) ∂lobby Y:=by
 rw [fare_R K P Y T θ κ y X H u h a Z f p]; apply integral_congr_ae; apply Eventually.of_forall; intro W; dsimp only; congr 1 -- tune congr
 unfold Day.mark; rw [MP.densify (μ:=fun _=>volume) (g:=fun (_:Y.Col) => Day.ticket (I:=Roll.Place Y) (trunc y)) (fun _=> Day.ticket_m _) (fun _ x=>Day.ticket_pos _ x (trunc_pos y))]
 let e:= MeasurableEquiv.curry Y.Col (Roll.Place Y) ℝ; let r:=chunk Y κ y Z f
 let g(x: Plan Y):= full Y y x • scale P Y T θ y X Z x • r (reach Y T θ y X Z W x)
 change _=∫ w:hot.Field Y,g (e.symm w); rw [← Law.apply_pres (g:=e) MP.volume_curry]
 · apply integral_congr_ae; apply Eventually.of_forall; intro x; dsimp only; rw [MeasurableEquiv.symm_apply_apply]; by_cases v: bed Y κ y (reach Y T θ y X Z W x)=Z; swap; · unfold g r chunk; simp only [if_neg v,smul_zero]
   by_cases h':Fares Y y x; rw [coinage K P Y T θ κ y X H u h a W v h', mul_comm, mul_smul]
   have he:full Y y x=0:=by obtain ⟨i,k⟩:=not_forall.mp h'; exact prod_eq_zero (mem_univ i) (Day.ticket_off _ _ k); -- tune semicolon
   rw [not_ne_iff.mp (fun v=> h' (incoming K P Y T θ κ y X H u h a v))]; unfold g; rw [he,zero_smul,zero_smul]
 refine Measurable.comp (g:=g) ?_ e.symm.measurable; have he : Measurable (scale P Y T θ y X Z):= measurable_const.mul (Real.measurable_exp.comp (watch_m ..)); refine Measurable.smul (f:=full Y y) (Finset.measurable_prod _ (fun i _=> (Day.ticket_m _).comp ?_)) (Measurable.smul he ((chunk_pay Y κ y Z f p).meas.comp ((reach_m Y T θ y X).comp (f:=fun x:Plan Y=>(W,x)) (by fun_prop))))
 unfold hot.entry Function.curry; fun_prop
end YM.CF.BProof.Release.Sky
