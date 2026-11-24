import YM.CF.Tarn.Lite
import YM.CF.Neige.Wit
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
open Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare
variable {H:Support c}{M N:Monk G S}{j:ℕ}
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal Gauges PhysicalNext.OrderedAffine2B.SymRows Locations Channels
variable {K:Teller G}
section
variable (g:Site c→SU.group.El) (T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(M:Monk G S) (h:K.Funds S T)
include h
lemma collectG (u:Run (M.zoo x) (j+1)) (p:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x): pes T x q d l (shiftZ g M) u=pes T x q d l M u:=by
 obtain ⟨σ,a,H,A⟩:=h.feeds; rw [← h.high] at H; have he:=gaugeH T M.key M.park x M.V M.k q d (M.bush x) g H (funds_branch h); have hv:=letter_edge he u; obtain ⟨hQ,hT⟩:=letterZ he p hf hm (fun _=>Iff.rfl) l (funds_branch h) H u; unfold pes
 exact congrArg₂ (·+·) (congrArg₂ (·+·) (congrArg (-(1/2:ℝ)*·) hv) (congrArg ((1/2:ℝ)*·) hQ)) hT
omit h in
lemma priceBeds(r:ℕ)(o:Site c):beds T x q d l M r o= ∑ v:Run (M.zoo x) (r+1), plant S o (stave v)*pes T x q d l M v:=by
 refine Eq.symm (Finset.sum_of_injOn stave stave_inj.injOn (fun v p=> mem_univ _) ?_ (fun v _=> congrArg (plant S o (stave v)*·) (paved _ _ _ _ _ _).symm)); intro w p t; rw [show pave T x q d l w M= 0 from ?_,mul_zero]; apply dif_neg (fun h=> t ⟨h.choose,mem_univ _,h.choose_spec⟩)
lemma groundX(p:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x) (o:Site c): Quill T x q d l (shiftZ g M) o= Quill T x q d l M o:=by
 unfold Quill; apply sum_congr rfl; intro i _; rw [priceBeds,priceBeds]; exact sum_congr rfl fun v _=> congrArg (plant S o (stave v)*·) (collectG g T x q d l M h _ p hm hf)
lemma vita (s:Signed)(b:Site c)(p:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x)(u:Run ((clue S s b M).zoo x) (j+1)):
 pes T x q d l (clue S s b M) u=pes T x q d l M ((calendar x M.key M.park s b).onKey∘u):=by
 obtain ⟨σ,a,H,A⟩:=h.feeds; rw [← h.high] at H; have he:=Char.turned T M.key M.park x M.V M.k q d (M.bush x) s b H (funds_branch h); obtain ⟨hQ,hT⟩:=letterZ he p hf hm (fun e=>green_map ..) l (funds_branch h) H u
 unfold pes; rw [show (clue S s b M).bush x= _ from gen x S s b M]; exact congrArg₂ (·+·) (congrArg₂ (·+·) (congrArg (-(1/2:ℝ)*·) (letter_edge he u)) (congrArg ((1/2:ℝ)*·) hQ)) hT
omit h in
lemma prime_o{b:Site c}(i: Run ((clue S s b M).zoo x) (j+1))(o:Site c): plant S o (stave i)=plant S (affine s b o) (stave ((calendar x M.key M.park s b).onKey ∘i)):=by -- b add
 let u:= stave i 0; let X:= StepData.sendSites s b; let A:=grove S u; let V:= stave ((calendar x M.key M.park s b).onKey∘i) 0
 have hx:grove S V= Finset.map X.toEmbedding A:=by
    apply Finset.coe_injective; rw [coe_map,grove_x]; unfold A; rw [grove_x]; exact Tensor.moves_points ..
 have hp: affine s b o∈grove S V ↔ o ∈ A:=by rw [hx]; change X o∈ _↔ _; rw [Finset.mem_map_equiv,X.symm_apply_apply]
 change (if o ∈ A then (A.card:ℝ)⁻¹ else 0)=if _∈grove S V then _ else _; exact if_ctx_congr hp.symm (fun _=>by change _=((grove S V).card:ℝ)⁻¹; rw [hx,card_map]) (fun _=>rfl)
lemma turnQuill(s:Signed)(b:Site c)(p:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x)(o:Site c): Quill T x q d l (clue S s b M) o= Quill T x q d l M (affine s b o):=by
 unfold Quill; apply sum_congr rfl; intro i _; rw [priceBeds,priceBeds]; let Q:=calendar x M.key M.park s b; let U:= Equiv.arrowCongr (Equiv.refl (Fin (i+2))) Q.onKey; rw [← Equiv.sum_comp U]; exact sum_congr rfl fun v _=> congrArg₂ (·*·) (prime_o _ _ _ _) (vita T x q d l M h s b p hm hf v)
end
end YM.CF.Tarn
