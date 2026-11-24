import YM.CF.Muse.Pure
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> (LeanV (Single Kx))
-- Exact resolve PH.Wick all shares.SupportX both senses. 
variable (p q: Single (mid P B))(Tg:Rill.Arch G t)(W: Meter TailB G t)(Y:Meter Grave G t)(g_: Odd G.count.val)(t':0<t)(kR:ℕ)
local notation "ρ"=> Support (Domain P B)
local notation "PX" b:max a:max=> (twigExt (b,a))
local notation "β"=> bring t' Tg
local notation "Xm"=> cala G S g_ t t' W Y Tg kR
-- reindex independent True Tilt.Axis. Metric after PE.Z.W. EACH (p,q) coarse independent shape.ALL order consensus
variable (F':RegBudget (mid P B))(DΦ:Finset (Scree.Hub (mid P B)))
local notation "Xρ"=> (γl x (Domain P B))
local notation "KΩ"=> (Finset (Support (Domain P B)))
local notation "SX"=> (StackL F' DΦ)
-- stack includes all.Slip combined separately. ANY charges.
local notation "ρk"=> (inbool (Domain P B) x)
variable (X: Finset (Support (Domain P B)))(U:Pane (mid N B))
local notation "Fv"=> (pulled G (bring t' Tg) W SX X)
local notation "tU"=> (bring t' Tg)
local notation "LI"=> (frame_w Fv)
variable (u:∀ i∈ DΦ,∀ (W':Pane (mid P B)), Flour (camp i.val.2) ((F' i W').val))
include t'
include u
-- localized docks for reanchor tariff exactly first endpoint. Edge h. support.C. Without revolution. 
variable (i:Scree.Hub (mid P B))(p₁ p₂:Rock (mid P B))(q₁ q₂:Rock (mid N B))(Y Z:Support (Domain P B))
local notation "Θ"=> lyric G t' W (F' i) Y Z p₁ p₂ q₁ q₂ 1 Tg
local notation "oQ"=> (S.ratio.parent i.val.1)
variable(Qx:TailB→Support (Domain P B)→Toll (Iota G))(pR:∀ i B,Suite (badge _) (pinH G t true) (pinH G t false) B (Qx i B) (W i B))
variable {u0:ℝ}(h: Prism.Rock (mid P B))
local notation "vZ"=> (hatY S)
omit u
variable (hv:S.ratio=ratio G)
include g_ t' hv pR
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
variable (hiZ:Cube.node p₁.1∈ i.val.2)(hj:Cube.node p₂.1∈ i.val.2)(hY:Y∈inbool (Domain P B) x)(hZ:Z∈inbool (Domain P B) x)
variable (S':BudgetPoint)(hy:Heir.Short S S' i.val.2)(hΩ:S'.B≤ 2*radiusB x)
local notation "GG"=> oQ
variable (O: Eire.Ride S)(Zμ:Support (Domain N B))(hQ:O= Stilo.beamH Zμ)(hK:Lattice.halo (45*(1+radiusB x)) {S.ratio.parent i.val.1} ⊆ Zμ)
include hiZ hY hΩ hy
local notation "Z_"=> Lattice.halo
local notation "A_"=> (hatY S)
abbrev ventK(x:ℝ)(n:ℕ):ℕ:=45*(1+radiusB x)+ n
local notation "ΦR"=> Z_ (ventK x kR) ({oQ}:Finset SN)
lemma quench (b:Bool)(v:fyL G b W tU Y p₁ q₁ ≠0):Lattice.halo kR (hatY S Y) ⊆ ΦR:=by
 let hq:=(zones Tg W g_ t' i p₁ q₁ Y Qx pR hv hiZ hY S' hy hΩ b v).2
 intro j p; obtain ⟨x,u,t⟩:=halo_spec.mp p; obtain ⟨y,l,rfl⟩:=mem_image.mp u; exact halo_spec.mpr ⟨oQ,mem_singleton_self _,(separation_triangle ..).trans (le_trans (add_le_add (hq y l) t) (by unfold cirQ ventK; omega))⟩
include hK
lemma quip(b:Bool)(p:fyL G b W tU Y p₁ q₁ ≠0):Z_ kR (A_ Y)=∅ ∨ ¬Disjoint Zμ (Z_ kR (A_ Y)):=by
 by_cases t:Y=∅; · left; simp only [t]; simp [Lattice.halo,hatY]
 obtain ⟨y,l⟩:= nonempty_iff_ne_empty.mpr t; have hx:= (zones Tg W g_ t' i p₁ q₁ Y Qx pR hv hiZ hY S' hy hΩ b p).2 y l; right; intro v; exact Finset.disjoint_left.mp v (hK (halo_spec.mpr ⟨oQ,mem_singleton_self _,hx.trans (by unfold cirQ; omega)⟩)) (halo_subset kR (hatY S Y) (mem_image_of_mem _ l))
omit t' g_ hiZ hY hΩ hy hK hv pR
lemma mastH {α:Type*}[Fintype α][DecidableEq α](P S: Finset α)(p:S=∅ ∨ ¬Disjoint P S): Stilo.beamH P ⊔ Stilo.beamH S=Stilo.beamH (P∪S):= p.elim (fun v=>by rw [v,Stilo.beam_b,sup_bot_eq, union_empty]) (fun v=> Stilo.boundH _ _ v) -- need explicit p
include t' g_ hiZ hj hY hΩ hy hK hv pR hQ hZ
local notation "H_Y" Y:max=> (halo kR (hatY S Y)) -- use implicit RN
variable (hZ':Zμ ⊆ Lattice.halo (ventK x kR) {S.ratio.parent i.val.1})
include hZ'
lemma gable(v:Θ ≠ 0):∃ Q':Palot.leaf (Site (Domain N B)),Stilo.beamH Q'.val= primeY (kR:=kR) Y Z O ∧ Q'.val ⊆ ΦR:=by
 let O':= oQ; let A:=halo kR (hatY S Y); let X:= halo kR (hatY S Z)
 have h: fyL G true W tU Y p₁ q₁≠0:= fun z=> v (by simp [lyric,z]); have h':fyL G false W tU Z p₂ q₂≠0:= fun z=> v (by simp [lyric,z])
 have q:=quip Tg W g_ t' kR i p₁ q₁ Y Qx pR hv hiZ hY S' hy hΩ Zμ hK true h; have hz:=quip Tg W g_ t' kR i p₂ q₂ Z Qx pR hv hj hZ S' hy hΩ Zμ hK false h'
 have ht:oQ∈ Zμ:= hK (halo_subset _ _ (mem_singleton_self _)); let Q':= Zμ∪A∪X; refine ⟨⟨Q',oQ,mem_union_left _ (mem_union_left _ ht)⟩,?_ , Finset.union_subset (Finset.union_subset hZ' (quench Tg W g_ t' kR i p₁ q₁ Y Qx pR hv hiZ hY S' hy hΩ true h)) (quench Tg W g_ t' kR i p₂ q₂ Z Qx pR hv hj hZ S' hy hΩ false h')⟩
 unfold primeY mark_l; rw [hQ, mastH _ _ q, mastH (Zμ∪A) X]; exact hz.imp id fun h v=>h (Disjoint.mono_left subset_union_left v)
 -- maybe defeq
end YM.CF.Oath
