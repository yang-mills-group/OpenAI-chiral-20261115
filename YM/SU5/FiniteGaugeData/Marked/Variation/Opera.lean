import YM.SU5.FiniteGaugeData.Marked.Variation.Triptych
/-! # Portal for the actual one-step push -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Fock Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange
open Common VolumeCape VolumeCape.Atlas VolumeCape.Mesh VolumeCape.Cane VolumeCape.Read
open Push.GridApprox
attribute [local instance] opCStarAlgebra
variable (S:Finset Cover)(C:Side)(K:ℕ→ℝ)(N P:Side)
variable (G:Ratio N P)(A:StepData (More N) (More P))(j:ℕ)(Q:Op SU.Slot)(M:Male)(ho: Odd G.count.val)(χ:Chi)(γ β:ℝ)(l:Loom N){D w:ℕ}(p:LaurentRadius j G.count D)
variable (v:Measurable l)(b:A.patch.Branches A.kernel SU.group)(h:0<γ)(g:2*γ<firstRadius SU.group) {f:PairsC→ℂ}(q:Coeff true S f)(u:Chorus)(hf : AtSupport (treble u) (region S N) (knot N u f))(W:Fields P)
-- formula after exact projection at T

def panelX (F:rawF C S)(r:Courses C S)(x:Hall C S):=
  let V:= replant S N (Common.pairs C K S r x)
  mist C S A β F x.1 • gathered G j Q M ho χ γ (wholeZ N u) W V
lemma xp (F:rawF C S)(r:Courses C S)(p:LaurentRadius j G.count D)(h:0<γ)(g:2*γ<firstRadius SU.group) : Envelope (panelX S C K N P G A j Q M ho χ γ β u W F r):=by
 let Y:= replant S N ∘ Common.pairs C K S r
 apply Girt.kitE (fun x:Hall C S=> mist C S A β F x.1) _ (fun (k:ℂ)(s:FC (Single P))=> k • s) (by exact continuous_fst.smul continuous_snd)
 · exact Envelope.compactC ((mist_c C S A).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
 exact Env.along (g:=fun x=>(W,Y x)) (env_gathered G j Q M ho χ γ p h g (wholeZ N u) (Girt.rite_c _)) (measurable_const.prodMk ((replant_b S N).comp (pairs_m C K S r)))

variable (s:Dream.Haven C K N l)(T:Finset Cover)(sT:S⊆T)(H:halo (Advance.nearZero D) (region S N)⊆ region T N)(y:Tipping T N C)
include y q sT
private lemma hear (r:Courses C T)(x:Hall C T):
  f (Prod.map (onC N) (onC N) (replant T N (Common.pairs C K T r x)))=amount C K T f r x:=by
 refine q.locus _ _ ?_ ?_
 all_goals rintro ⟨a,i⟩ p _; dsimp only [Prod.map_fst,Prod.map_snd,replant]; rw [onC_spec]; exact within T N C y ⟨a,sT p⟩ _ _
private lemma song (r:Courses C T)(x:Hall C T):
 let V:= replant T N (Common.pairs C K T r x)
 gathered G j Q M ho χ γ (knot N u f) W V = amount C K T f r x • gathered G j Q M ho χ γ (wholeZ N u) W V :=by
 intro V
 have he:knot N u f V=amount C K T f r x • wholeZ N u V:=by unfold knot wholeZ; rw [show f _=_ from hear S C K N q T sT y r x]
 unfold gathered avgF before; simp_rw [he,map_smul,←Finset.smul_sum]; rw [smul_comm]

include v h g hf q s b H p
lemma cabaret (x : ℝ)
    (Y:∀ (F:rawF C T)(r:Courses C T),
      ‖∫ z:Hall C T,amount C K T f r z • panelX T C K N P G A j Q M ho χ γ β u W F r z ∂law C T‖ ≤ x):
    ‖pushMark G A j Q M ho χ γ β l (knot N u f) W‖ ≤ x:=by
 let Z(v:Fields N):=gathered G j Q M ho χ γ (knot N u f) W v
 have eZ: Envelope Z:= Env.along (g:=Prod.mk W) (env_gathered G j Q M ho χ γ p h g (knot N u f) hf.env) (measurable_const.prodMk measurable_id)
 have tZ (a c:Fields N)(p':Agrees (region T N) a.1 c.1)(t:Agrees (region T N) a.2 c.2): Z a= Z c:= gather_dep G j Q M ho χ γ p _ hf W W (fun _ _ _=> rfl) a c (agrees_mono p' (Finset.image_subset_image sT)) (agrees_mono t H)
 obtain ⟨μ,k₀,_,k⟩:=s
 let m(i:A.Choices) (x':Orbit N):ℝ:=A.noise β (A.prediction W.1 i) x'.1
 let r(x':Orbit N):=Z (drawn l x')
 have lq (i:A.Choices):‖∫ z:Orbit N,m i z • r z∂city N‖ ≤ x:=by
    simp_rw [←Complex.coe_smul]
    rw [show ∫ z:Orbit N,(m i z:ℂ) • r z ∂city N = _ from triangle C K T N l v k P Z eZ tZ A β (A.prediction W.1 i) y]
    apply (norm_integral_le_of_norm_le_const (C:=x) (Filter.Eventually.of_forall fun a=>?_)).trans_eq
    · simp
    have hi:=Y (A.prediction W.1 i ∘ stretch (porch C T) N) (chooseCourse C T N a)
    unfold Z; simp_rw [song S C K N P G j Q M ho χ γ q u W T sT y, smul_comm (mist _ _ _ _ _ _) (amount _ _ _ _ _ _)]; exact hi
    -- 
 have hm (i:A.Choices):Envelope (m i):= Env.along (g:=Prod.fst) (show Envelope (fun x':Pane N=> A.noise β (A.prediction W.1 i) x') from Env.compact (by unfold StepData.noise StepData.penaltyWeight; fun_prop)) measurable_fst
 have t (i:A.Choices):Integrable (fun z=> m i z • r z) (city N):= Env.integrableX (Env.scale (hm i) (Env.along (g:=drawn l) eZ (drawn_m l v))) _
 rw [outright G A j Q M ho χ γ β l p v b h g _ hf.env]
 let F(i:A.Choices):ℝ:= A.likelihood W.1 i
 change ‖∫ z:Orbit N,(∑ i:A.Choices, F i*m i z) • r z∂city N‖ ≤ x
 simp_rw [Finset.sum_smul, mul_smul]; rw [integral_finsetSum]; swap
 · intro i _; exact (t i).smul (F i)
 simp_rw [integral_smul]; apply (norm_sum_le ..).trans
 have hz(i):0≤ F i:= A.likelihood_pos ..
 exact (sum_le_sum (g:=fun i=>F i*x) (fun i _=>by rw [norm_smul,Real.norm_of_nonneg (hz _)]; exact mul_le_mul_of_nonneg_left (lq i) (hz i))).trans_eq (by rw [←sum_mul,A.chosen b,one_mul])
#check norm_integral_le_of_norm_le_const
section
variable {X I:Type*}(N P:I→Side)(L:Side)(x:∀ i, (P i).val=(N i).val*L.val)
local notation "g₀"=> bead N L P x
variable (A:(i:I)→ StepData (More (N i)) (More (P i)))(Q:I→Op SU.Slot)(M:I→Male)(ho:Odd L.val)(BF:I→ℝ)(W:(i:I)→Fields (P i)){n t:Side}(Z:StepData n t)(s0:∀i,(A i).kernel=Z.kernel)
variable (F:I→ rawF C T)(d:I→ Common.Courses C T){Y Y':ℝ}(vA:LaurentRadius j L D)
variable (a:∀i,‖BF i‖ ≤ Y)(a':∀i, ‖Q i‖ ≤ Y')
omit s h H v sT y hf b p q -- s shadows old s
include a a' s0 g vA
-- need h and remove g references γ ok
include h
lemma matchbox : Menu (T:=fun i=>FC (Single (P i))) (fun (i:I)(z:Hall C T)=> panelX T C K (N i) (P i) (g₀ i) (A i) j (Q i) (M i) ho χ γ (BF i) u (W i) (F i) (d i) z):=by
 let T':=(Set.Icc (-Y) Y) ×ˢ (Set.univ : Set (rawF C T × Hall C T))
 have he:Menu (T:=fun _:I=>ℂ) (fun i (z:Hall C T)=> mist C T Z (BF i) (F i) z.1):=by
    have hz:Deal (I:=I) (T:=fun _=> Hall C T) (fun _ (z:Hall C T)=>z):= deal_of_one (show Measurable id from measurable_id) isCompact_univ (fun _=>Set.mem_univ _)
    refine Menu.clip ((Deal.pure (X:=Hall C T) (T:=fun _:I=>ℝ) BF).prod ((Deal.pure (T:=fun _:I=>rawF C T) F).prod hz)) (isCompact_Icc.prod isCompact_univ:IsCompact T') (fun i x=>?_ ) (mist_c C T Z)
    exact ⟨abs_le.mp (a i),Set.mem_univ _⟩
 let t' (i:I)(z:Hall C T):= replant T (N i) (Common.pairs C K T (d i) z)
 have ht: Menu (T:=fun i=> FC (Single (P i))) (fun i (z:Hall C T)=> gathered (g₀ i) j (Q i) (M i) ho χ γ (wholeZ (N i) u) (W i) (t' i z)):=by
    refine stitched N L P x j D vA ho M Q a' W t' ?_ χ γ h g u
    let J:= Σ i :I, Edge (Seat (N i))
    exact graft_deal T C (fun z y=> (Common.pairs C K T z y).2) (fun z=> measurable_snd.comp (pairs_m C K T z)) (fun i:J=> d i.1) (fun i:J=> N i.1) (fun i=>i.2)
 refine (he.scale ht).congr ?_
 intro i z; unfold panelX; change _ • _= _ • _; congr 1
 unfold mist noiseLink StepData.penaltyZ StepData.penaltyWeight; rw [s0]
end
end YM.CF.Buffered.Afterglow.Satin
#print axioms YM.CF.Buffered.Afterglow.Satin.matchbox
