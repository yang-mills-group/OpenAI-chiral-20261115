import YM.CF.Lich.Pole
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
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
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
open Rel
variable (R':ℕ)(Z:Tab S→FileM (Domain N B) SU.group)(K': Tab S→DirP (Domain N B))
-- Enough via combination even if no CakeF on Φ available explicit.Tighten plan κ in Φ independent references.Path
lemma ork{σ B' E:ℝ}(p:Wick Z K' R' n σ B' E): Tips R' K':= fun i t u=>⟨p.axis _ _ _,fun z w b hv hx=>by rw [p.patch i z t u hv]; exact (p.vows ..).1.reads _ _ hx⟩ -- tune Vote.V width.Locale
lemma orm{σ B' E:ℝ}(p:Woven Z K' R' r n σ B' E):Tips R' K':= fun i t u=>⟨p.dawn _ _ _,fun z w b hv hx=>by rw [p.tracks i z t u hv]; exact (p.crew ..).1.reads _ _ hx⟩
abbrev ηδ := Tarn.Coin T x A.hash q A.vita A.rota θ α l
abbrev ξδ:=Facet.snowG G T q x A.unit γ θ l Q' A.hot
abbrev μδ:= fun y:Tab S=>fame T y q x θ l
local notation "b₀"=> radiusB x
local notation "m"=> Domain N B
structure Census (k b:ℕ): Prop where
 tag : (A.post+100)*b₀ ≤ b
 toe : j*b₀ ≤ b
 line : b₀+1+k ≤ b
 mask: coverB l j*b₀ ≤ b
 hero :∀ i ∈({A.mup,A.etap,A.xip}:Finset ℕ),i*b₀+R' ≤ b
 pureT: R'+1 ≤ b
 oath: R'+R'+1≤ b
 witX: Tips R' A.muK
 note : Tips R' A.etaD
 wise : Tips R' A.xiD
 witR : waysS R' (μδ A)
 quote : waysS R' (ηδ A)
 scene : waysS R' (ξδ A)
variable (k b:ℕ)(V':Rent0 G e) -- V redundant
variable{M:Monk SU.group S}{X:Support (Domain N B)}(H:Duo SU.group S U M X)(p:Ready T x)(hv:1000≤radiusB x)
variable (o:Site (Domain N B))(g:Kind S (U.park,U.k) (M.park,M.k) X)(t:Census A R' k b)(r0:Beat.shadows (o:=o) X b)
local notation "Vt"=> (j*b₀)
include H p hv t r0
lemma wish_k : wish A U o= wish A M o:=by
 unfold wish; have hp:(l+76)*radiusB x ≤ b:= (Nat.mul_le_mul_right _ (by omega)).trans t.tag; refine congrArg (-β *·) (congrArg averaged (funext fun i=> ?_)); unfold rush; simp only [filter_filter,sum_filter]; apply sum_congr rfl; intro u w; by_cases he:herald S i u=o
 · simp only [he,true_and]; simp only [gateL U H o _ r0 (d:=Vt) (i:=o) (by rw [separation_self]; exact (zero_add _).le.trans t.toe)]; split
   next z=>
    have hg:Virt S (dense T x q θ l β i u) X:=calm i u p hv (by rw [he]; exact Subset.trans (Corona.halo_mono hp (Subset.refl _)) r0); exact shotB_loc hg H.toBeat
   rfl
 simp only [he,and_false,↓reduceIte]
include g
lemma peri_p (hz:0< β) : per A U o=per A M o:=by
 unfold per yurn; refine congrArg Complex.ofReal (congrArg₂ (·+·) (congrArg₂ (·+·) ?_ (bluntB A U H p hv o b r0 t.tag t.toe)) (artB A U H p hv o b r0 t.tag)); refine congrArg₂ (·+·) (congrArg₂ (·+·) ?_ (wish_k A U R' k b H p hv o t r0)) ?_
 · unfold footS; refine congrArg (-β *·) (congrArg Complex.re ?_); exact oaths U H g o b r0 t.witR t.witX t.pureT t.oath t.toe ((Nat.add_comm ..).trans_le (by simpa only [add_comm] using (t.hero _ (mem_insert_self ..)))) -- weird
 refine sum_congr rfl fun i v=>opus_p T x q θ l β j i (by rw [(mem_filter.mp v).2]; exact Subset.trans (Corona.halo_mono t.mask (Subset.refl _)) r0) p hv hz H.toBeat
lemma fisc{a c d d':ℝ}{Z: nomA N P B→ℂ}(W':Rent0 G e)(z:S.ratio=ratio G)(ht:0< β)(hx:Tally Q' Z a d d' c n)(u:Panel A X k V V')(hq:Panel A X k W W'): burnS A U V W o= burnS A M V' W' o:=by
 unfold burnS Muster.lore; rw [peri_p A U R' k b H p hv o g t r0 ht, oaths U H g o b r0 t.quote t.note t.pureT t.oath t.toe (t.hero A.etap (by simp)),oaths U H g o b r0 t.scene t.wise t.pureT t.oath t.toe (t.hero A.xip (by simp))]; congr 3
 unfold prum; have hv:= aroundBk X r0 ((show separation o o+ (b₀+1+k)=_ from by rw [separation_self,zero_add]).trans_le t.line); simp only [gateL U H o b r0 (d:=Vt) (i:=o) (by rw [separation_self]; exact (zero_add _).le.trans t.toe), echoF A V V' z hx o X u hv, echoF A W W' z hx o X hq hv]
end Muster
end YM.CF.Lich
