import YM.CF.Arena.Purch
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
variable {K:Teller G}
open Push.Uniform (bolt)
lemma voice_y(T:Tube G S)(F:Forest S.ratio)(p:Body 1 c)(q:SU.group.ColorIndex):chair T F (flaw G p q)=bolt (p,q):=by
 ext ⟨i,j⟩; change Pi.single (M:=fun _=>SU.group.Color) p (jewelG G q) i j= _; by_cases h:i=p
 · subst i; by_cases h:j=q <;> simp [h,Push.Uniform.bolt,jewelG]
 simp [h,jewelG,Push.Uniform.bolt]
lemma fameK {A B: Tab S}{i:Site c}(h:Ready T x)(p:1000≤radiusB x)(H:Kind S A B (pavilion (horn x l) i)): fame T A q x d l i=fame T B q x d l i:=by
 unfold fame; apply congrArg (((Fintype.card Signed:ℂ))⁻¹ • ·) -- tune
 refine Finset.sum_congr rfl fun s _=>sum_congr rfl fun j v=>?_ ; have hz:herald S s j=i:= (mem_filter.mp v).2; funext U; exact congrArg (fun y:ℝ=>(y:ℂ)) (calm (l:=l) (q:=q) (d:=d) (β:=0) (M:=bunk S A U) (N:=bunk S B U) s j h p (X:=pavilion (horn x l) i) (hz.symm ▸ (show Beat.shadows (o:=i) (pavilion (horn x l) i) (horn x l) from Subset.refl _)) ⟨fun _ _=>Iff.rfl,H.site,fun i t=>H.edge i (t (mem_insert_self ..)),KinT H,fun _ _ _=>rfl,fun _ _=>rfl, fun _ _=>rfl⟩)
lemma hoop_sum{E:Type}[AddCommMonoid E](f:Along S→E)(s:Signed): ∑ p:Site c,∑ i∈ hoop S s p,f i=∑ i,f i:=by unfold hoop; simp_rw [sum_filter]; rw [sum_comm]; simp
lemma up_q(k:S.Choices)(t:Tab S)(U:Config G c)(q:Chi)(d:ℝ)(h:K.Funds S T) : let M:=bunk S t U; let g:=M.sent x T q d l 0;
 (∑ i,fame T t q x d l i U)=(mainTerm T.high (grainA T.up (Stores.till x)) g+noiseTaylor S U g t.2-mainTerm T.low (grainA T.down (Hors.cart x S.patch.L)) U:ℝ):=by
 intro M g; rw [←wise _ h g U t.2]; unfold fame averaged heed; simp_rw [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]; rw [←mul_sum,sum_comm]; simp_rw [hoop_sum]; simp_rw [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_sum] -- tune
 congr 1; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=> congrArg (fun v:Along S→ℝ=>(v j:ℂ)) (bluff q x d l T M i rfl) -- tune
lemma hut_v(T:Tube G S)(t:Tab S)(x d:ℝ)(v:Mast G c)(C:ℝ)(u:ℝ)(h:K.Funds S T)(l k:ℕ)(ht:Fire T x t.1 t.2 l u k C v): let w:=u•v; let M:=bunk S t (facadeX G w); let X:= M.sent x T q d l 0;
 (∑ i,fame T t q x d l i M.V)= (Hors.hut T x t.1 t.2 l w:ℂ):=by
 intro w M X; rw [up_q t.2 _ _ _ _ h]; have hp: glow T x t.1 t.2 u q d l (0:Directions G f) v=0:= by change _ *ᵥ visitX t.1 x ((tint G (Active (bareStores S) x t.1)).symm 0)=(0:Fish (Key t.1 G)); rw [map_zero,map_zero,Matrix.mulVec_zero]
 let a:= sol S T t.2 x t.1 l w; have hv:X= increment (replica S.ratio (facadeX G w)) (trays S x t.1 a):=by
    apply (shineU (β:=0) (q:=q) (d:=d) (g:=M) rfl v (s:=u) rfl ht).trans ?_ -- tune parameter A bad
    change increment (replica S.ratio (facadeX G w)) (trays S x t.1 (coupling 0 • glow T x t.1 t.2 u q d l 0 v+a))=_; rw [show glow T x _ _ u _ _ _ _ v= _ from hp,smul_zero,zero_add]
    -- tune
 change ((mainTerm _ _ X+noiseTaylor S _ _ _- _ :ℝ):ℂ)= _; rw [show mainTerm T.high _ X+noiseTaylor S M.V X M.k= clipped T x t.1 t.2 (meetVar w a) from ?_]
 · unfold Hors.hut Hors.avail Hors.firmX; simp only [one_smul]; rfl -- tune
 rw [←clip_actual,rack_actual,hv]
lemma mat_sum (T:Tube G S)(l i:ℕ)(u:Tab S)(h:satX (∑ j,fame T u q x d l j) =ᶠ[𝓝 0] Complex.ofRealCLM ∘ Hors.hut T x u.1 u.2 l ∘ chair T u.1) (ht:∀ j,ContDiffAt ℝ (i:ℕ∞ω) (satX (fame T u q x d l j)) 0)(P:ContDiffAt ℝ (i:ℕ∞ω) (Hors.hut T x u.1 u.2 l) 0)(hz:∀ j:Fin i→ Push.Uniform.Primary c G, |Push.Uniform.entry (Hors.hut T x u.1 u.2 l) 0 j| ≤ C):Prox (fame T u q x d l) i C:=by
 intro y z; rw [sumF (fame T u q x d l) i _ ht]; let a(i):= (y i,z i); let v(i):= flaw G (y i) (z i); let H:= Hors.hut T x u.1 u.2 l; let L:= chair T u.1; let Q:=Complex.ofRealCLM; have hp':ContDiffAt ℝ (i:ℕ∞ω) H (L 0):= (map_zero L).symm ▸ P
 unfold cake; rw [show iteratedFDeriv ℝ i (satX _) 0= iteratedFDeriv ℝ i (Q∘ H ∘ L) 0 from (h.iteratedFDeriv ℝ i).eq_of_nhds,Q.iteratedFDeriv_comp_left (hp'.comp _ L.contDiff.contDiffAt) le_rfl, Push.Uniform.iter_lin_at (L:=L) hp', map_zero,_root_.smul_apply,norm_smul]; change _*‖Q ((iteratedFDeriv ℝ i H 0) (fun j=> L (v j)))‖ ≤ _; apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
 · unfold L v; simp_rw [voice_y]; exact ((Complex.norm_real _).trans_le (hz a)) -- tune
 rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos i)
end YM.CF.Arena
