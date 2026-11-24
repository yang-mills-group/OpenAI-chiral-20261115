import YM.SU5.WakeFields.MoonRoom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open YM.CF.BPress (PL NPL)
variable {F G:ℝ→ℝ}
open Vow Sour Swell Ione
namespace Rate
namespace LocalLimit
open Jet
namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open LitCurrent Buffered Sault Vow.TreasuryFog Furrow Mew Cadre Roots Afterglow
open scoped YM.CF.Mew
variable {i k s r : ℕ} {a moV γ Δ W:ℝ}
local notation "m"=> cell (Y.ir i) P.block P.R.L s
local notation "ℒ"=> (Y.voyage i).CapeT s
local notation "Q"=> RootBook Y i k s
local notation "M0"=>funde P.K.j (Q).J.M m
local notation "T0"=>Moire.bloom (Q).J.P
variable (w:ℝ) (F : LitCurrent.Pattern (funde P.K.j (RootBook Y i k s).J.M (cell (Y.ir i) P.block P.R.L s)) (Moire.bloom (RootBook Y i k s).J.P) r P.d a moV)
local notation "Rκ"=> cloth Y w F
local notation "Rτ"=> mock Y w F
local notation "pκ"=> purchased (s:=s) (i:=i) (k:=k) Y
-- second panel is the **true Loom** of that same CapeT. New chemistry only at this density step.
abbrev truePaper (j:Site m)(V:Orbit m): FC (Single m) := Rτ j (V.1,ℒ V)
variable (M : Site (cell (Y.ir i) P.block P.R.L s)→Bag (cell (Y.ir i) P.block P.R.L s)) (Qℓ : ∀ x, Booked Y w F x (M x) γ Δ)
variable {I:Type} [Fintype I] [LinearOrder I] (o : I→Site (cell (Y.ir i) P.block P.R.L s))(L : List I)
local notation "F0"=> wholePin m I (Q).K
local notation "σ"=> Cube.node ∘ o
variable {Λu t:ℕ}(τ : Ids (cell (Y.ir i) P.block P.R.L s))(K:Key I→ Rinse (Seat (cell (Y.ir i) P.block P.R.L s)) (Copy (cell (Y.ir i) P.block P.R.L s)))
variable (Q₁ : Armed Y (s:=s) (k:=k) (i:=i) o τ (M ∘o) (fun i=> truePaper Y w F (o i)) t Λu W K)
abbrev spineY (z:Key I) (u:ℕ) := polarized Q σ F0 K u (0:Key I→ RegBudget m) τ (outPlant (Q).p (spaceD (Q).p F0 K u τ) (Cube.node∘o) P.R.L.val) z
abbrev berthPaper (u:ℕ) (F':Mark (cell (Y.ir i) P.block P.R.L s)) (V:Orbit m): ℂ:= letterRead (F' (V.1,ℒ V)) (tipI (fun z=>denZ (spineY Y (k:=k) o τ K z u) P.U ℒ V) L)

private lemma paper_comm {N:Side}{A B:Support (More N)}{u t:FC (Single N)}(p : Sector (modesIn N A) false u)(q : Sector (modesIn N B) false t) (g:Disjoint A B) : Commute u t:= by
 have ht:Disjoint (modesIn N A) (modesIn N B):=disjoint_left.mpr fun i u v=>disjoint_left.mp g ((modes_at ..).mp u) ((modes_at ..).mp v)
 exact (p.apart q ht).trans (one_smul ..)

include Q₁ Qℓ
lemma pierK (u:L.length ≤ Λu) (p: ψS (Cube.node∘o) L)
    (Z:(L.map o).Pairwise (fun i j=> Disjoint (pκ i) (pκ j)))
    (U:Orbit m)(H:Rue.FleetS (Q).p.threshold U.1) :
    tipI (fun z=>denZ (spineY Y (k:=k) o τ K z Λu) P.U ℒ U) L=acts ((L.map o|>.map (mock Y w F)).prod (U.1,ℒ U)) (denZ Q P.U ℒ U) := by
 obtain ⟨C,A⟩:= Q₁.bill; let V(j):=mock Y w F j; let f(x:Fields m):= (L.map (fun i=>V (o i))).prod x
 let P':Fields m:=(U.1,ℒ U)
 have hp: L.Pairwise (fun i j => Commute (V (o i) P') (V (o j) P')) := (List.pairwise_map.mp Z).imp (fun w=> paper_comm ((Qℓ _).cares P') ((Qℓ _).cares P') w)
 have hv: (L.map (fun j=>V (o j) P')).prod=(L.map o|>.map V).prod P':= by
    suffices t:∀ l:List I,(l.map (fun j=> V (o j) P')).prod=(l.map o|>.map V).prod P' from t _; intro l; induction l with | nil=> rfl| cons i l ih=> exact congrArg (V (o i) P' * ·) ih
 exact (A.priceTip P.U ℒ U Λu o W 2 P.R.L t τ (fun j=> truePaper Y w F (o j)) P.R.L.val L u p H (projects_here Y i k s U).1 hp).trans (congrArg (fun f:FC (Single m)=>acts f (denZ Q P.U ℒ U)) hv)

variable {S : Support (More (cell (Y.ir i) P.block P.R.L s))} (F':Mark (cell (Y.ir i) P.block P.R.L s)) (pF:AtSupport false S F') -- notation capture hazard!
local notation "Fκ"=> F'*(L.map o|>.map (cloth Y w F)).prod

include pF
lemma exactFare (u:L.length ≤ Λu) (p: ψS (Cube.node∘o) L)
    (Z:(L.map o).Pairwise (fun i j=> Disjoint (pκ i) (pκ j)))
    (h:∀ j∈L.map o,Disjoint S (pκ j))
    (U:Orbit m)(H:Rue.FleetS (Q).p.threshold U.1) :
    letterRead ((F'*(L.map o|>.map (cloth Y w F)).prod) (U.1,ℒ U)) (denZ Q P.U ℒ U)=berthPaper (s:=s) (k:=k) Y o L τ K Λu F' U := by
 unfold berthPaper; rw [pierK Y w F M Qℓ o L τ K Q₁ u p Z U H]; -- tune `•` defeq
 let X:Fields m:=(U.1,ℒ U); let Pm:= F' X; let E:= (L.map o|>.map (cloth Y w F)).prod X; let V:= (L.map o|>.map (mock Y w F)).prod X
 let W:=denZ Q P.U ℒ U; let MΩ:=mateK m
 change inner ℂ MΩ (acts (Pm*E) W)=inner ℂ MΩ (acts Pm (acts V W)); rw [←act_mul]
 have he(f:Site m→ Mark m)(t:∀ i,Sector (modesIn m (pκ i)) false (f i X))(Z:List (Site m))(u:∀ j∈Z,Disjoint S (pκ j)) : Commute Pm ((Z.map f).prod X) := by
    induction Z with
    | nil=> exact Commute.one_right _
    | cons i Z ih=> exact (paper_comm ((pF.allV X).sector) (t i) (u i List.mem_cons_self)).mul_right (ih fun j p=> u j (List.mem_cons_of_mem _ p))
 have h1:Commute Pm E:=he _ (fun i=> ((Qℓ i|>.mark).allV X).sector) _ h; have h2: Commute Pm V:= he _ (fun i=> (Qℓ i).cares X) _ h
 rw [h1.eq,h2.eq, act_mul,act_mul,← act_inner, ←act_inner V,show acts (star E) MΩ= acts (star V) MΩ from productBra Y w F M γ Δ Qℓ _ Z X]
omit Qℓ Q₁ pF
lemma pierGap (u:Force_M (RootBook Y i k s).p.B (Cube.node∘o) t) (p:10 ≤ (Q).p.B)(v:ψS (Cube.node∘o) L) : (L.map o).Pairwise (fun i j=> Disjoint (pκ i) (pκ j)) := by
 apply List.pairwise_map.mpr; refine (List.pairwise_map.mp v).imp (fun {x y} h=>?_); refine disjoint_left.mpr ?_
 intro j a b; let B:ℕ:= (Q).p.B
 obtain ⟨i,u',w⟩:=halo_spec.mp a; rw [mem_singleton.mp u'] at w
 obtain ⟨k,u',z⟩:=halo_spec.mp b; rw [mem_singleton.mp u',separation_comm] at z
 let K:=(Cube.node (o x)); let Z:=Cube.node (o y)
 have he:separation K Z ≤ 24*B+24*B:= (separation_triangle K j Z).trans (Nat.add_le_add w z)
 have hv:= u.1 x y h; change B^3+B^3+B+B < separation K Z at hv; change 10 ≤ B at p
 nlinarith only [he,hv,p,Nat.one_le_pow 2 B (by omega)] -- tune
include Qℓ Q₁ pF
lemma pierCompass (u:L.length≤Λu) (p: ψS (Cube.node∘o) L)
    (Z:(L.map o).Pairwise (fun i j=> Disjoint (pκ i) (pκ j)))
    (h:∀ j∈L.map o,Disjoint S (pκ j)) (v:s<Y.uv k)(g:(Y.voyage i).kick≤k):
    let D:= berthPaper Y (s:=s) (k:=k) o L τ K Λu F'; let T:=partitionZ (RootBook Y i k s) P.U ((Y.voyage i).CapeT s);
    Integrable D (city m) ∧ T≠0 ∧ Journey.compass Y i k s (F'*(L.map o|>.map (cloth Y w F)).prod)= (∫ i,D i∂city m)/T := by
 intro D T
 let Z':= Fκ; let M'(V:Orbit m):=letterRead (Z' (V.1,ℒ V)) (denZ Q P.U ℒ V)
 have hn(J:List (Site m)):AtSupport false univ (J.map (cloth Y w F)).prod:= by induction J with | nil=> exact AtSupport.oneM _| cons i J ih=> exact ((Qℓ i|>.mark.mono (subset_univ _)).mulM ih)
 obtain ⟨f₁,t',e⟩:= Tapestry.funds Y s i k (f:=Z') (((pF.mono (subset_univ _)).mulM (hn (L.map o))).env) g v.le
 have Ag:Rue.IsleB SU.group (RootBook Y i k s).p.threshold:= by
    rw [show (RootBook Y i k s).p= Y.meter.a s from (((Y.voyage i).X (Y.uv k)).pull.owns s v.le).width.symm]; exact ((Y.voyage i).paths k).paid.can.isle s
 have he:M'=ᵐ[city m] D:=by filter_upwards [Rate.ae_fleet (n:=m) Ag] with x t; exact exactFare Y w F M Qℓ o L τ K Q₁ F' pF u p Z h x t
 exact ⟨(Integrable.congr (f:=M') f₁ he),t',e.trans (congrArg (·/T) (integral_congr_ae he))⟩

end Preparation
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.pierCompass
