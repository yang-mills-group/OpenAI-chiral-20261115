import YM.SU5.Interaction.Source
import YM.SU5.LitCurrent.Spun
import YM.SU5.LitCurrent.Reached
import YM.SU5.LitCurrent.Copy
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
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F)
local notation "tape" i:max=> (Y.voyage i)
local notation "Coord" i:max k:max=> (tape i).X (Y.uv k)
variable {Pay ξC Γϕ:ℝ}{n u:ℕ}{Tξ:Hove.Grant P.K.j 2}
variable (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
local notation "xt" => hat P.R.L P.x
local notation "Aκ" v:max=> Y.meter.a v
local notation "Rt" i:max k:max s:max => (RootBook Y i k s)
local notation "Ω" i:max k:max=> cell (Y.ir i) P.block P.R.L k
open LitCurrent Buffered Sault Vow.TreasuryFog
variable {i k s r:ℕ}{a b c v w:ℝ}
local notation "Λ"=> P
local notation "Q"=> RootBook Y i k s
local notation "Qp"=>(Q).p
local notation "Ω🌍"=> cell (Y.ir i) P.block P.R.L s
local notation "M0"=> funde P.K.j (Q).J.M Ω🌍
local notation "T0"=> Moire.bloom (Q).J.P
local notation "ℒ"=> (Y.voyage i).CapeT s
local notation "D"=> (Qp).B/10
local notation "β"=> hueW P.R.L (xt s)
abbrev cloth (w:ℝ)(E:LitCurrent.Pattern M0 T0 r P.d a v)(x:Site Ω🌍): Mark Ω🌍:= budded P.R.L (xt s) (physicalSeed ℒ Qp D w x E)
abbrev mock (w:ℝ)(E:LitCurrent.Pattern M0 T0 r P.d a v)(x:Site Ω🌍): Mark Ω🌍:= budded P.R.L (xt s) (surrogate ℒ Qp D w x E)
abbrev purchased (x:Site Ω🌍): Sa Ω🌍:= grooveB 24 Qp (node x)

abbrev matA (Y:Course P F)(r:ℕ)(a b v w:ℝ):ℝ→ℝ:=mintedJ P.R.L (Y.meter.a 0) r P.h w a b v
abbrev matB (Y:Course P F)(r:ℕ)(a b v w:ℝ):ℝ→ℝ:=mintedB P.R.L (Y.meter.a 0) r P.h w a b v
local notation "κ" => pinpr P.R.L
structure Booked (w:ℝ)(E: LitCurrent.Pattern M0 T0 r P.d a v)(x:Site Ω🌍)(M:Sour.Bag Ω🌍)(c d:ℝ):Prop where
    nest : Nest P.U Q ℒ P.J.n 24 (node x) P.h (rScale Qp) (fun v=>mock Y w E x (v.1,ℒ v)) M c d
    mark : AtSupport false (purchased (s:=s) (i:=i) (k:=k) Y x) (cloth Y w E x)
    covar: covariant (cloth Y w E x)
    cares (U:Fields Ω🌍):Fock.Sector (modesIn Ω🌍 (purchased (s:=s) (i:=i) (k:=k) Y x)) false (mock Y w E x U)
    same (U: Fields Ω🌍): acts (star (cloth Y w E x U)) (mateK Ω🌍)=acts (star (mock Y w E x U)) (mateK Ω🌍)
    pose (ℓ:w=1/2)(f:Sweep Ω🌍)(U V:Fields Ω🌍)(h:V.1=flashA f U.1) :
        let z:= Urn.lotB f.charge (det_S f) (γS f)
        z (cloth Y w E x U)=Scroll.hush (det_S f) (cloth Y w E (pose f x) V) ∧
        z (mock Y w E x U)=Scroll.hush (det_S f) (mock Y w E (pose f x) V)

-- exact x layout prices, including thrust; permit maskTick transformations even at period seams.
variable (w:ℝ)(h: MaskPoint Y r s i k a b)(Fore:LitCurrent.Pattern (funde P.K.j (RootBook Y i k s).J.M (cell (Y.ir i) P.block P.R.L s)) (Moire.bloom (RootBook Y i k s).J.P) r P.d a v)
include h
lemma allBooked (x:Site Ω🌍)(g:0< κ (xt s)):
    ∃ M, Booked Y w Fore x M (matA Y r a b v w (xt s)) (matB Y r a b v w (xt s)*κ (xt s)) :=by
 obtain ⟨M,t⟩:= commits Y w h x Fore g
 refine ⟨M,t,?_,?_ ,fun i=>?_,fun V=>?_,fun e s' U V p=>?_⟩
 · exact ((physical_support ℒ Qp _ w x Fore h.C).mono (words_fit Qp x _ h.reach)).smulM (↑β:ℂ)
 · intro g x'; apply Eq.trans (b:=(↑β:ℂ) • twist (quantU (tradew Ω🌍 g)) (physicalSeed ℒ Qp D w x Fore x')); · exact congrArg (fun v:FC (Single Ω🌍)=> (↑β:ℂ) • v) (physical_moves ℒ Qp _ w x Fore h.C g x')
   exact (twist_scalar ..).symm
 · exact (surrogate_sector w h.C x Fore _ h.reach h.escap i).scale (↑β:ℂ)
 · unfold cloth mock budded; rw [Pi.smul_apply,Pi.smul_apply,star_smul,star_smul,act_smul,act_smul,centered_bra]
 subst w; let f':=det_S s'; let U':=Urn.lotB s'.charge f' (γS s'); have hp:cSignX (s'.charge.xor f') (β:ℂ)=(β:ℂ):= by cases s'.charge.xor f'<;> simp [cSignX]
 constructor
 · change U' ((↑β:ℂ) • _) = Scroll.hush f' ((↑β:ℂ) • (_:FC (Single Ω🌍)))
   rw [show ∀ Y':FC (Single Ω🌍),U' ((↑β:ℂ) • Y')= (↑β:ℂ) • U' Y' from fun t=>(Urn.visage ..).trans (congrArg (fun v:ℂ=>v • U' t) hp), show U' (physicalSeed ℒ Qp D _ x Fore U)=_ from posesY x h.C Fore s' U V p]; change _ • Scroll.hush f' _= _; cases f' <;> simp
 change U' ((↑β:ℂ) • _) = Scroll.hush f' ((↑β:ℂ) • (_:FC (Single Ω🌍)))
 rw [show ∀ Y':FC (Single Ω🌍),U' ((↑β:ℂ) • Y')= (↑β:ℂ) • U' Y' from fun t=>(Urn.visage ..).trans (congrArg (fun v:ℂ=>v • U' t) hp), show U' (surrogate ℒ Qp D _ x Fore U)= _ from poses_surrogate x h.C Fore s' U V p]; change _ • Scroll.hush f' _=_; cases f'<;>simp
omit h
local notation "GΩ"=> cloth Y w Fore
local notation "Mκ"=> mock Y w Fore
local notation "ω𝚱"=> mateK Ω🌍
variable (M: Site (cell (Y.ir i) P.block P.R.L s)→ Sour.Bag (cell (Y.ir i) P.block P.R.L s))(C D':ℝ) (f:∀ x,Booked (s:=s) (i:=i) (k:=k) Y w Fore x (M x) C D') (J:List (Site (cell (Y.ir i) P.block P.R.L s))) (q:J.Pairwise (fun x y=> Disjoint (purchased (s:=s) (i:=i) (k:=k) Y x) (purchased (s:=s) (i:=i) (k:=k) Y y)))
-- product equality at the bra. for any marked/tie/comparison on same data.
include f q
lemma productBra(U:Fields Ω🌍) :acts (star ((J.map GΩ).prod U)) ω𝚱=acts (star ((J.map Mκ).prod U)) ω𝚱:=by
 let P'(V:Site Ω🌍→ Mark Ω🌍)(x y):=Commute (Mκ x U) (V y U)
 have h(W:Site Ω🌍→ Mark Ω🌍)(t:∀ x,Fock.Sector (modesIn Ω🌍 (purchased (s:=s) (i:=i) (k:=k) Y x)) false (W x U))(x y: Site Ω🌍)(p:Disjoint (purchased (s:=s) (i:=i) (k:=k) Y x) (purchased (s:=s) (i:=i) (k:=k) Y y)):P' W x y:=by
    have ht:Disjoint (modesIn Ω🌍 (purchased (s:=s) (i:=i) (k:=k) Y x)) (modesIn Ω🌍 (purchased (s:=s) (i:=i) (k:=k) Y y)):=disjoint_left.mpr fun i u v=>disjoint_left.mp p ((modes_at ..).mp u) ((modes_at ..).mp v)
    exact (((f x).cares U).apart (t y) ht).trans (one_smul ..)
 have hh(V:Site Ω🌍→ Mark Ω🌍)(x:Site Ω🌍)(l:List (Site Ω🌍))(v:∀ y∈l,P' V x y): (Mκ x U)*(l.map V).prod U=(l.map V).prod U * Mκ x U:=by
    induction l with
    | nil=> simp
    | cons i l p=>
       simp only [List.map_cons,List.prod_cons,Pi.mul_apply]; rw [←mul_assoc,(show Commute _ _ from v i (by simp)).eq,mul_assoc,p fun y t=> v y (List.mem_cons_of_mem _ t),mul_assoc]
 induction J with
 | nil=>rfl
 | cons l J p=>
    obtain ⟨u,v⟩:=List.pairwise_cons.mp q
    have hx:=congrArg star (hh GΩ l J (fun x t=> h _ (fun y=>(f y|>.mark.allV U).sector) l x (u x t)))
    have hp:=congrArg star (hh Mκ l J (fun x t=> h _ (fun y=>(f y).cares U) l x (u x t)))
    rw [star_mul,star_mul] at hx hp
    rw [List.map_cons,List.prod_cons,Pi.mul_apply,List.map_cons,List.prod_cons,Pi.mul_apply,star_mul,act_mul,(f l).same,←act_mul,hx,star_mul,hp,act_mul,act_mul,p v]

omit q f
abbrev reelSymbol (M:Sour.Bag Ω🌍)(U:Orbit Ω🌍): FC (Dwell Ω🌍) := ∑ i: Aura Ω🌍, M i U
include f
lemma pilot_product (U:Orbit Ω🌍) (g:IsStarProjection (spar P.K.j (Q).J.M (ℒ U)))(z:Wave (Dwell Ω🌍)): let H:=pilotH P.U Q ℒ U g; H (acts ((J.map (fun l=> reelSymbol (s:=s) (i:=i) Y (M l) U)).prod) z)= acts ((J.map Mκ).prod (U.1,ℒ U)) (H z):=by
 intro H; induction J generalizing z with
 | nil=> simp only [List.map_nil,List.prod_nil,Pi.one_apply,act_one]
 | cons i J h=>
    simp only [List.map_cons,List.prod_cons,Pi.mul_apply,act_mul]; rw [(f i|>.nest.science),h] -- need defeq
omit f
abbrev atPilot (U:Orbit Ω🌍):=
 pilotH P.U Q ℒ U (projects_here Y i k s U).1
include f q
lemma signedPrice (g:(Y.voyage i).kick ≤ k)(u:s<Y.uv k):let t:=markedRead (J.map GΩ).prod ℒ (denZ Q P.U ℒ); let V:=partitionZ Q P.U ℒ; let Z(U:Orbit Ω🌍):= inner ℂ ω𝚱 (atPilot (s:=s) (i:=i) (k:=k) Y U (acts ((J.map fun j=>reelSymbol (s:=s) (i:=i) Y (M j) U).prod) (Cadre.poseL _ (fueled Qp (Q).K U))))
 FullBill.Priced P.V Q P.U ℒ (Y.charge s) (Y.debt s) ∧ V≠0 ∧ Integrable Z (city Ω🌍)∧ t/V=(∫ u,Z u∂city Ω🌍) / V :=by
 intro T' V Z -- erase
 have hp:= Y.each_level i k s g u.le
 have hx(U:Orbit Ω🌍): denZ Q P.U ℒ U= atPilot (s:=s) (i:=i) (k:=k) Y U (Cadre.poseL _ (fueled Qp (Q).K U)):=by
    have ht:= showUp (R:=Q) P.U ℒ U (show IsStarProjection _ from (projects_here Y i k s U).1) 0 (Q).K
    rw [show exponentL Qp 0 U.1= 0 from (by simp [exponentL,numbE]),exp_zero,one_mul,add_zero] at ht; exact ht
 let Fj(U:Orbit Ω🌍):=letterRead ((J.map GΩ).prod (U.1,ℒ U)) (denZ Q P.U ℒ U)
 have hh:Fj=Z:=by
    funext U; unfold Fj; rw [letterRead, ContinuousLinearMap.comp_apply]; change inner ℂ ω𝚱 _=_
    rw [←act_inner,productBra Y w Fore M C D' f J q,act_inner,hx]; refine congrArg _ (Eq.symm (pilot_product Y w Fore M C D' f J U _ _))
 have hz:Envelope (J.map GΩ).prod:=by
    suffices h:∀ J:List (Site Ω🌍), AtSupport false univ (J.map GΩ).prod from (h J).env
    intro J; induction J with | nil=> exact AtSupport.oneM _| cons i l p=> exact (((f i).mark.mono (subset_univ _)).mulM p)
 have hT:Measurable ℒ:= ((Y.voyage i).ownership s).paid.bill
 refine ⟨hp,hp.valid,hh ▸ (show Integrable Fj _ from ?_),congrArg (fun (fr: Orbit Ω🌍→ℂ)=>(∫ u,fr u∂city Ω🌍)/ V) hh⟩
 exact Marks.read_int (fun U=> (J.map GΩ).prod (U.1,ℒ U)) (Marks.can_read _ _ _ _ hp) (show Envelope (fun U:Orbit Ω🌍=> (J.map GΩ).prod (U.1,ℒ U)) from Girt.snap hz (measurable_fst.prodMk hT)) -- tune
end Preparation
end LocalLimit
end Rate
end YM.CF.Py
