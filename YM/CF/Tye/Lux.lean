import YM.CF.Tye.Stare
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "Y"=> clue S s b M
local notation "V"=> shiftZ g M
local notation "F"=> cedar M
variable (h:K.Funds S T)(hp:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hv:120 ≤ radiusB x)(hz:0 < m)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(ht: LocalRatio A.vita)(hi:0 < A.rota)(hm:4*A.rota < A.vita.radius)(hb:0 < A.beta)
local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x
local notation "Z"=> mid N B
local notation "j'"=> A.loft
local notation "q"=> A.trot
local notation "Q"=> A.LawQ
local notation "L'"=> A.post
local notation "J"=> A.vita
local notation "R"=> A.rota
local notation "v'"=> A.room
local notation "H"=> A.hot
local notation "β"=> A.beta
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "X"=> kist M
variable (f:Sweep (mid N B))(W U': Rent0 G e)(i:Site (Domain N B))
variable (ph:S.ratio=ratio G)(t:tyke G A.LawQ)(xw:A.Beds.val=(1,1))
local notation "W'"=> male e G f W
local notation "N'"=> rot f M
local notation "A'"=> clue S f.s (Facet.pasta f) M
local notation "Λ"=> chart f
local notation "Ω"=> M.key.dome (j'*radiusB x)
variable (w' z:ℝ)
local notation "I"=> calendar x M.key M.park
lemma exam_k(j:Bond (Domain P B))(i:M.zoo x)(u:i∈(locals M.key M.key x M.park ((A.loft+104)*radiusB x))ᶜ)(v:i.val.val=j): Lich.Muster.boon A j M= broad A.trot A.room (tape (M.fuel x T A.trot A.room A.post A.beta) i):=by
 unfold Lich.Muster.boon; let hw:∃ i∈(locals M.key M.key x M.park ((A.loft+104)*radiusB x))ᶜ,i.val.val=j:=⟨i,u,v⟩; rw [dif_pos hw]; have he:hw.choose=i:=Subtype.ext (Subtype.ext (hw.choose_spec.2.trans v.symm)); rw [he]
lemma boon_b {D E:Monk SU.group S}{j u:Bond (Domain P B)} (F': D.zoo x≃E.zoo x)(p:∀ i,i.val.val=j ↔ (F' i).val.val=u)(m':∀ i, i∈(locals D.key D.key x D.park ((A.loft+104)*radiusB x))ᶜ ↔ F' i∈(locals E.key E.key x E.park ((A.loft+104)*radiusB x))ᶜ)(h:∀ i,broad q v' (tape (D.fuel x T q v' L' β) i)= broad q v' (tape (E.fuel x T q v' L' β) (F' i))): Lich.Muster.boon A j D=Lich.Muster.boon A u E:=by
 let Qw:=(locals D.key D.key x D.park ((j'+104)*radiusB x))ᶜ; by_cases k:∃ i∈Qw,i.val.val=j
 · obtain ⟨r,f,k⟩:=k; rw [exam_k A D j r f k,exam_k A E u (F' r) ((m' _).1 f) ((p _).1 k)]; exact h r
 unfold Lich.Muster.boon; rw [dif_neg k, dif_neg]; rintro ⟨i,v,w⟩; obtain ⟨a,rfl⟩:=F'.surjective i; exact k ⟨a,(m' _).2 v,(p _).2 w⟩ -- syntax m' binder Lean fail

abbrev satR(S: StepData (Domain N B) (Domain P B))(s:Signed)(b:Site (Domain N B)):Equiv.Perm (Sat S):= Equiv.sumCongr (shiftFaces s (S.ratio.embed b)) (Equiv.sumCongr (StepData.sendBonds s b) (diagram s b S))
lemma port_k(i:Bond (Domain P B)): portF A M w' z (.inr (.inr i))= Lich.Muster.boon A i M:=rfl
include h hp hz hv
local notation "NY"=> M.sent x T q v' L' β
lemma sat_s0(i:Cell d'): portF A Y w' z (.inl i)=portF A M w' z (satR S s b (.inl i)):=by
 unfold portF; change (if _ then _ else _)=(if _ then _ else _); rw [space_s T x q v' L' β s b M h hp hz hv]; apply if_congr
 · change _↔ shiftFaces s _ i∈ (nearFace S _)ᶜ; simp_rw [mem_compl]; exact not_congr (far_f s b M.key _ i)
 · simp only [tokenF, AnalyticBridge.Annulus1AD.profile,rise_b,clue,Locations.book,mem_map_equiv,Equiv.symm_symm]
 rfl
lemma sat_s1(i:Bond d): portF A Y w' z (.inr (.inl i))=portF A M w' z (satR S s b (.inr (.inl i))):=by
 unfold portF; change (if _ then _ else _)=(if _ then _ else _); rw [space_s T x q v' L' β s b M h hp hz hv]; apply if_congr
 · change _↔ StepData.sendBonds s b i∈ (nearNoise _)ᶜ; simp_rw [mem_compl]; exact not_congr (far_b ..)
 · exact wing_t s b M.key NY M.V M.k (funds_branch h) q x w' z i
 rfl
lemma sat_s2(i:Bond d'): portF A Y w' z (.inr (.inr i))=portF A M w' z (satR S s b (.inr (.inr i))):=by
 rw [show satR S s b (.inr (.inr i))=Sum.inr (Sum.inr (diagram s b S i)) from rfl,port_k,port_k]; apply boon_b A (D:=clue S s b M) (E:=M) (j:=i) (I s b).onKey
 · intro j; change _↔ diagram s b S j.val.val=diagram s b S i; exact (diagram s b S).injective.eq_iff.symm
 · intro i'; simp_rw [mem_compl]; apply not_congr; unfold locals; simp only [mem_filter,mem_univ,true_and]; exact witnessP M.key s b i'.val.val _
 intro k; rw [space_f T x q v' L' β s b M h hp hz hv]; unfold Next.SectorChange.broad; erw [move_tape (onBond (page s b M)) (canE x s b M).onKey _ k,LinearIsometry.norm_map]; rfl
lemma sat_s(i:Sat S): portF A Y w' z i=portF A M w' z (satR S s b i):=by
 rcases i with i|i|i; exact sat_s0 A M s b h hp hv hz w' z i; exact sat_s1 A M s b h hp hv hz w' z i; exact sat_s2 A M s b h hp hv hz w' z i
lemma sat_g0(i:Cell d'):portF A V w' z (.inl i)=portF A M w' z (.inl i):=by
 unfold portF; rw [gauge_s T x q v' L' β g M h hp hz hv]; dsimp only [Sum.elim_inl]; simp only [tokenF,AnalyticBridge.Annulus1AD.profile, toll_gauge]
lemma sat_g1(i:Bond d):portF A V w' z (.inr (.inl i))=portF A M w' z (.inr (.inl i)):=by
 unfold portF; rw [gauge_s T x q v' L' β g M h hp hz hv]; dsimp only [Sum.elim_inl,Sum.elim_inr]; exact if_congr Iff.rfl (gear_t M.key NY M.V M.k g (funds_branch h) q x w' z i) rfl
lemma sat_g2(i:Bond d'):portF A V w' z (.inr (.inr i))=portF A M w' z (.inr (.inr i)):=by
 rw [port_k,port_k]; apply boon_b A (D:=shiftZ g M) (E:=M) (j:=i) (Equiv.refl (M.zoo x)) (fun _=>Iff.rfl) (fun _=>Iff.rfl); intro i; rw [buzz g M q x β v' h L' m hp hz hv]; unfold Next.SectorChange.broad Slate.Pogo; rw [move_tape,LinearIsometry.norm_map] -- tune
lemma sat_g(i:Sat S):portF A V w' z i=portF A M w' z i:=by
 rcases i with i|i|i; exact sat_g0 A M g h hp hv hz w' z i; exact sat_g1 A M g h hp hv hz w' z i; exact sat_g2 A M g h hp hv hz w' z i
include hA
lemma sat_f0(i:Cell d'): portF A F w' z (.inl i)=portF A M w' z (.inl i):=by
 unfold portF; rw [echo_s T x q v' L' β M h hp hz hv hA]; dsimp only [Sum.elim_inl]; simp only [tokenF,AnalyticBridge.Annulus1AD.profile,mint_b]
lemma sat_f1(i:Bond d): portF A F w' z (.inr (.inl i))=portF A M w' z (.inr (.inl i)):=by
 unfold portF; rw [echo_s T x q v' L' β M h hp hz hv hA]; dsimp only [Sum.elim_inl,Sum.elim_inr]; exact if_congr Iff.rfl (Rink.echo_t M.key NY M.V M.k (funds_branch h) q x w' z i) rfl
lemma sat_f2(i:Bond d'): portF A F w' z (.inr (.inr i))=portF A M w' z (.inr (.inr i)):=by
 rw [port_k,port_k]; apply boon_b A (D:=Rink.cedar M) (E:=M) (j:=i) (Equiv.refl (M.zoo x)) (fun _=>Iff.rfl) (fun _=>Iff.rfl); intro i; rw [echo_f T x q v' L' β M h hp hz hv hA]; unfold Next.SectorChange.broad; rw [move_tape,LinearIsometry.norm_map]; rfl
lemma sat_f(i:Sat S): portF A F w' z i=portF A M w' z i:=by
 rcases i with i|i|i; exact sat_f0 A M h hp hv hz hA w' z i; exact sat_f1 A M h hp hv hz hA w' z i; exact sat_f2 A M h hp hv hz hA w' z i
end YM.CF.Tye
