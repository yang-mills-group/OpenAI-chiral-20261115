import YM.SU5.Selected.Airy.Stubs
import YM.CF.Lattice.Reference
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Topology Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset Fock Rush Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
local instance : CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
variable (N:Side)(U:Jill.Male)
def tip := freeze (fun i:Site N=> bar 4 U.val (mel i))
lemma tipped: IsStarProjection (tip N U):=by
 have h(i:Site N):= bar_frames 4 U.val (base_subset_realCube zone_pos (mel_h i)) (mel_away i) U.property
 unfold tip; refine ⟨?_,?_⟩; · unfold IsIdempotentElem; rw [freeze_mul]; exact congrArg freeze (funext fun i=> (h i).1)
 change (freeze _)ᴴ=_; rw [freeze_star]; exact congrArg freeze (funext fun i=> (h i).2)
variable (n p:ℕ)(G:Side)(g:8≤G.val)(e:n≥4)
local notation "Y"=> artisans G n p e
local notation "V"=> plinth G n p e
local notation "Fp"=>children G n p
local notation "ρ"=> Real.exp (-(1/2))
private lemma standing (x: Site N) : IsStarProjection (bar 4 U.val (mel x)):=by
 obtain ⟨a,b⟩:=bar_frames 4 U.val (base_subset_realCube zone_pos (mel_h _)) (mel_away _) U.property; exact ⟨a,b⟩
-- large Male uniform trade. insert phase p, frame construction freezes AFTER e chosen.
def mtn : Filter Jill.Male:= (atTop:Filter Side).comap Subtype.val
lemma mtn_out (F:Jill.Male→Prop)(h:∀ᶠ k in mtn,F k):∃ S:Side,∀ k:Jill.Male,S ≤ k.val→ F k:=by
 obtain ⟨A,p,q⟩:= h; obtain ⟨x,t⟩:= mem_atTop_sets.mp p; exact ⟨x,fun k hk=> q (show (k:Side)∈A from t _ hk)⟩ -- notation
private lemma jetUniform : TendstoUniformlyOn (fun i:Jill.Male=> zen∘mixL 4 i.val ∘ tmap ∘ joinBin) (zen ∘ tough ∘ joinBin) mtn foyer:=by
 -- could use climbs via uniform continuity, linear zen. adapt.
 rw [←tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact foyerCompact,tendstoLocallyUniformlyOn_iff_forall_tendsto]; intro x u; let l:=𝓝[foyer] x; let g:=mtn ×ˢ l
 let p:= Prod.snd (α:= Jill.Male) (β:=Facet3 ×ℝ); have h: Tendsto p g l:= tendsto_snd; let j:=tough ∘ joinBin; have hp:Tendsto (j∘p) g (𝓝 (j x)):= (thermalV x u).tendsto.comp h
 have he:Continuous tmap:=by unfold tmap; fun_prop
 let k(i:Jill.Male): Facet3 ×ℝ→Momentum:= mixL 4 i.val ∘ tmap ∘ joinBin; have ht: Tendsto (fun i:Jill.Male×(Facet3×ℝ)=> k i.1 i.2) g (𝓝 (j x)):= tendsto_pi_nhds.mpr (fun a=> gulch (M':=Subtype.val ∘ Prod.fst) (tendsto_comap.comp (show Tendsto Prod.fst g mtn from tendsto_fst)) (((he.comp join_cont).continuousOn (s:=foyer) x u).tendsto.comp h) (Filter.Eventually.of_forall (fun i:Jill.Male×_=> i.1.property)) (banded u.1 _ u.2) (pureV u.1 _) a (by filter_upwards [h.eventually (show ∀ᶠ x' in l,x'∈foyer from eventually_mem_nhdsWithin)] with v z; exact b_base (banded z.1 _ z.2))) -- tune
 exact (((zen_c.tendsto (j x)).comp hp).prodMk_nhds ((zen_c.tendsto (j x)).comp ht)).mono_right (nhds_le_uniformity _)
include g
lemma general_bound : ∃ C:ℝ,0<C∧ ∀ x:Coast, ‖Fp x‖≤C ∧ ‖V x‖ ≤ C ∧ ‖Y x‖≤ C:=by
 obtain ⟨t,u,v⟩:= signal G n p e g; let X:C(Coast, Wq p):=⟨_,t⟩; let A:C(Coast,Wq p):=⟨_,u⟩; let B:C(Coast,Wq p):=⟨_,v⟩; refine ⟨‖X‖+‖A‖+‖B‖+1,by positivity,fun x=>?_⟩; constructor; · exact (X.norm_coe_le_norm x).trans (by linarith [norm_nonneg A,norm_nonneg B])
 exact ⟨(A.norm_coe_le_norm x).trans (by linarith [norm_nonneg X,norm_nonneg B]),(B.norm_coe_le_norm x).trans (by linarith [norm_nonneg X,norm_nonneg A])⟩
lemma backend_price (ε:ℝ)(d:0<ε): ∀ᶠ M:Jill.Male in mtn,∀ N:Side, ‖(1-tip N M)*freeze (Y∘ brim N)‖ ≤ ε:=by
 obtain ⟨C,pC,t⟩:= general_bound n p G g e
 have ht:= Metric.tendstoUniformlyOn_iff.mp jetUniform (ε/C) (by positivity); filter_upwards [ht] with v p' N;
 let P(x:Site N):= bar 4 v.val (mel x); let f:=fun x:Site N=>(1:Op SpinIdx); rw [tip,show (1:Op (Site N×SpinIdx))=freeze f from freeze_one.symm, ←freeze_sub,freeze_mul]; apply freeze_norm d.le; intro x
 let w:=brim N x; let T:=Y w; let L:=V w; let R:= (1:Op SpinIdx)-zen (mixL 4 v.val (mel x))
 change ‖(1-P x)*T‖≤ ε
 have hp: (P x)* (R*L)= R*L:=by
    have he:= lead true 4 v.val v.property (base_subset_realCube zone_pos (mel_h x)) (mel_away _)
    change P x * (R*Aop)= R*Aop at he; rw [← show Aop * L=L from plinth_plus ..]; rw [←Matrix.mul_assoc R,←Matrix.mul_assoc,he]
 let z:= (fun j:Fin 3=>pm x j.castSucc); let x':= (z,pm x 3); have h0: joinBin x'=pm x:=by change Ε z (pm x 3)=_; exact Fin.snoc_init_self _
 by_cases h:soap G (pier w)=0; · change ‖_*( (1-zen (utility w):Op SpinIdx)*V w)‖ ≤ _; simp [plinth,h, d.le]
 have e₁:x'∈foyer:= ⟨soap_back G (fun i:Fin 3=> pm_zone x i.castSucc) h, Set.Ioc_subset_Icc_self (show _∈deck from pm_zone x 3)⟩
 rw [show ( (1-P x:Op SpinIdx))*T=(1-P x) *(T-R*L) from (by rw [Matrix.mul_sub, Matrix.sub_mul _ (P x) (R*L), Matrix.one_mul,hp,sub_self,sub_zero])]; apply (Matrix.l2_opNorm_mul ..).trans; apply (mul_le_of_le_one_left (norm_nonneg _) ((standing N v x).one_sub.norm_le _)).trans; unfold T artisans; change ‖_* L-R*L‖≤_; rw [←Matrix.sub_mul]; apply (Matrix.l2_opNorm_mul ..).trans; have hV: ‖1-zen (utility w)-R‖ ≤ ε/C:=by
    have h:= (p' x' e₁).le; rw [dist_eq_norm] at h; change ‖zen (tough (joinBin x'))-zen (mixL 4 v.val (tmap (joinBin x')))‖≤_ at h; rw [h0] at h; unfold R w; rw [art_walk G x rfl (by assumption),sub_sub_sub_cancel_left]; exact (norm_sub_rev ..).trans_le h -- arg order
 exact (mul_le_mul hV (t w).2.1 (norm_nonneg _) (by positivity)).trans_eq (div_mul_cancel₀ _ pC.ne')
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms tipped
#print axioms backend_price
#print axioms general_bound
