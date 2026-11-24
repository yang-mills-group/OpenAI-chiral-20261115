import GaugeFieldConstruction.Masques
import YM.CF.Roots.Seat
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open HushP ModuleB Pastry
-- entries in PH houses: both endpoints. not represented yet as Mark physical.
open Housing
variable (o:Skye.Seat n)
-- A1 frame: g star transport from root at x. B_F paid using transported O.
-- algebra of insertion indices (complex linear in G). prove on paid subspace.
open Flot
set_option maxRecDepth 2800
variable (M:Tulip.Male)
open scoped YM.CF.Mew
-- offshore labels with price spaces. Use explicit coordinates separately
def G3: Submodule ℂ (leadF Gem Gem) where
 carrier:= { A| A.flip=A}
 zero_mem':= by change ((0:leadF Gem Gem).flip)=0; ext i j <;> rfl
 add_mem':=by intro x y p q; change _∈ _; ext i j; exact congrArg₂ (fun a b:ℂ=> a+b) (congrArg (fun u:leadF Gem Gem=> u i j) p) (congrArg (fun u:leadF Gem Gem=> u i j) q) -- tune
 smul_mem':=by intro x y p; change _; ext i j; exact congrArg (fun u:leadF Gem Gem=> x • (u i j)) (show y.flip=y from p)
def P03: Submodule ℂ Pal where
 carrier:= { X| SheetQ X}
 zero_mem':= SheetQ.blank
 add_mem':=by intro x y; exact SheetQ.plus
 smul_mem':= fun a _ u=> Layout.SheetQ.step u a
def P14: Submodule ℂ (OneF Views Pal) where
 carrier:= {x|∀ i,SheetQ (x i)}
 zero_mem':=by intro i; exact SheetQ.blank
 add_mem':=by intro x y p q i; exact SheetQ.plus (p i) (q i)
 smul_mem':=by intro a x p i; exact SheetQ.step (p i) a
def P25: Submodule ℂ (TwoF Views Pal) where
 carrier:= {x|∀ i j, SheetQ (x i j) ∧ x i j=x j i}
 zero_mem':=by intro i j; exact ⟨SheetQ.blank,rfl⟩
 add_mem':=by
    intro x y p q i j; exact ⟨SheetQ.plus (p i j).1 (q i j).1,congrArg₂ (fun a b:Pal=>a+b) (p i j).2 (q i j).2⟩
 smul_mem':=by intro a x p i j; exact ⟨SheetQ.step (p i j).1 a,congrArg (fun x:Pal=> a • x) (p i j).2⟩
def G15 : Submodule ℂ (ComG→L[ℝ]Pal) where
 carrier:={A|ViewsM A}
 zero_mem':= by refine ⟨fun _=>?_,fun _ _ _=>?_⟩ <;> simp -- tune
 add_mem':=by
    intro x y p q; refine ⟨fun i=>?_,fun g a i=>?_⟩
    · simp only [_root_.add_apply,mul_add, add_mul, p.binned,q.binned]
    simp only [_root_.add_apply,mul_add, add_mul,p.main,q.main]
 smul_mem':=by
    intro a x p; refine ⟨fun i=>?_,fun g b i=>?_⟩
    · change baseF false* (a • x i) *_= a • _; rw [Matrix.mul_smul, Matrix.smul_mul,p.binned]; try rfl
    change (a • x _) * KinX g= _ *(a • _); rw [Matrix.mul_smul,Matrix.smul_mul,p.main]; try rfl
abbrev Gκ:= leadF Gem Sut
abbrev J3:= P03
abbrev J4 := (G3 × P14)
abbrev J5 := Gκ× P25 × G15
abbrev Waves:= J3 × J4 × J5
-- finDim over C; fallback module finite via axes
abbrev bV0(V: Waves):= V.1
abbrev bV1(V: Waves):= V.2.1.2
abbrev bV2(V: Waves):= V.2.2.2.1
abbrev bF4(V: Waves):= V.2.1.1
abbrev bF5(V: Waves):= V.2.2.1
abbrev bm5(V: Waves):= V.2.2.2.2
def chartF(V:Waves):PalOne:= ( (bV0 V).val,(bV1 V).val,⟨(bV2 V).val, fun i j=> ((bV2 V).property i j).2⟩)
lemma chart_j(V:Waves): JetX (chartF V):=⟨(bV0 V).property,(bV1 V).property,fun i j=> ((bV2 V).property i j).1⟩
structure MetaB (V:Waves)(Q:InkD n)(p:BudgetPoint)(h:ℝ) : Prop where
 post : (bF4 V).val = fave p o Q
 mast : bF5 V = claw p o Q
 port : chartF V= winJ o M h (orbitPH (Q 1))
 mixed : (bm5 V).val = landA M o Q p h
lemma metaUnique (Q:InkD n)(p:BudgetPoint)(h:ℝ)(V W:Waves)(u:MetaB o M V Q p h)(t:MetaB o M W Q p h):V=W:=by
 have he : chartF V =chartF W:=u.port.trans t.port.symm
 exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Prod.ext (Prod.ext (Subtype.ext (u.post.trans t.post.symm)) (Subtype.ext (congrArg (fun i:PalOne=> i.2.1) he))) (Prod.ext (u.mast.trans t.mast.symm) (Prod.ext (Subtype.ext (congrArg (fun i:PalOne=>i.2.2.val) he)) (Subtype.ext (u.mixed.trans t.mixed.symm)))))
def exportM (P:PressB p X Q h c)(s:0≤h)(he:o=X.val.1) : Waves:=by
 let T:=orbitPH (Q 1); let u:=winJ o M h T; let F:=landA M o Q p h; let A:= fave p o Q; have hp: A.flip=A:= symm_f P s; let ζ:=claw p o Q
 have h:ViewsM F:= portalG M P; have v:JetX u:=whiskey o M P s
 exact (⟨u.1,v.1⟩,(⟨A,hp⟩, ⟨u.2.1,v.2.1⟩),ζ,⟨u.2.2.val,fun i j=>⟨v.2.2 i j, u.2.2.property i j⟩⟩,⟨F,h⟩)
lemma export_full (P: PressB p X Q h c)(s:0≤h)(t:o=X.val.1):MetaB o M (exportM o M P s t) Q p h:=⟨rfl,rfl,rfl,rfl⟩
lemma beanFlip {A:G3} : let V:= A.val; V.flip=V:= A.property
-- module finite & canonical norm. Norm `NormedAddCommGroup` conflicts for ℝ vs ℂ, choose restricted. First supply ℂ finite generic real CLM.
private lemma scarfE {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedSpace ℂ F][IsScalarTower ℝ ℂ F][FiniteDimensional ℝ E][FiniteDimensional ℝ F]: FiniteDimensional ℂ (E→L[ℝ] F):=Module.Finite.of_restrictScalars_finite ℝ ℂ _
private noncomputable abbrev Badge_Norm {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedSpace ℂ F][IsScalarTower ℝ ℂ F] (P: Submodule ℂ (E→L[ℝ] F)):NormedAddCommGroup P:=inferInstance
scoped instance κ_G3 : NormedAddCommGroup G3:= Badge_Norm (E:=Gem) (F:=Gem→L[ℝ]ℂ) G3
scoped instance κ_G15 : NormedAddCommGroup G15:= Badge_Norm (E:=ComG) (F:=Pal) G15
private noncomputable abbrev Badge_space {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedSpace ℂ F][IsScalarTower ℝ ℂ F](P:Submodule ℂ (E→L[ℝ]F)):NormedSpace ℂ P:=inferInstance
scoped instance κ_h3 : NormedSpace ℂ G3:= Badge_space G3
scoped instance κ_h15 : NormedSpace ℂ G15:= Badge_space (E:=ComG) (F:=Pal) G15
private lemma Badge_F {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedSpace ℂ F][IsScalarTower ℝ ℂ F][FiniteDimensional ℝ E][FiniteDimensional ℝ F](S:Submodule ℂ (E→L[ℝ]F)):FiniteDimensional ℂ S:=by letI:FiniteDimensional ℂ (E→L[ℝ] F):= scarfE; infer_instance
-- ABI declare instances per-grade with ?
instance finG3z : FiniteDimensional ℂ G3:= by exact Badge_F (E:=Gem) (F:=Gem→L[ℝ]ℂ) G3
instance finP14z : FiniteDimensional ℂ P14:=by
 letI:FiniteDimensional ℂ (OneF Views Pal):=scarfE (E:=Views) (F:=Pal)
 infer_instance
scoped instance finpN : NormedAddCommGroup P25:=Badge_Norm (E:=Views) (F:=OneF Views Pal) P25
scoped instance finpS: NormedSpace ℂ P25:=Badge_space (E:=Views) (F:=OneF Views Pal) P25
scoped instance finpF: FiniteDimensional ℂ P25:=Badge_F (E:=Views) (F:=OneF Views Pal) P25
instance finG15z: FiniteDimensional ℂ G15:= Badge_F (E:=ComG) (F:=Pal) G15
instance finGκz: FiniteDimensional ℂ Gκ:=scarfE (E:=Gem) (F:=Sut→L[ℝ]ℂ)
structure TPack (E:Type) where
 [G: NormedAddCommGroup E]
 [S: NormedSpace ℂ E]
 [F: FiniteDimensional ℂ E]
-- assert instances consistent by pack. afterwards scoped instances choose higher. type tokens
abbrev PackL : TPack J3:= {}
abbrev PackP : TPack P14 := {}
abbrev PackM : TPack P25 := {G:=finpN,S:=finpS,F:=finpF}
abbrev PackG : TPack G3 := {G:=κ_G3,S:=κ_h3,F:=finG3z}
abbrev PackH:TPack Gκ := { F:=finGκz}
abbrev PackS:TPack G15 := {G:=κ_G15,S:=κ_h15,F:=finG15z}
abbrev CartPack {A B:Type}(P:TPack A)(Q:TPack B):TPack (A×B):=by
 letI:=P.G; letI:=P.S; letI:=P.F; letI:=Q.G; letI:=Q.S; letI:=Q.F; exact {}
abbrev Packs_U := CartPack PackL (CartPack (CartPack PackG PackP) (CartPack PackH (CartPack PackM PackS)))
scoped instance (priority:=1500) kinnG : NormedAddCommGroup Waves:=Packs_U.G
scoped instance (priority:=1500) kinnS : NormedSpace ℂ Waves:=Packs_U.S
scoped instance (priority:=1500) kinnF: @Module.Finite ℂ Waves _ Packs_U.G.toAddCommGroup.toAddCommMonoid (Packs_U.S.toModule):= Packs_U.F
scoped instance (priority:=1550) kinnA : AddCommGroup Waves:= kinnG.toAddCommGroup
scoped instance (priority:=1550) kinnL : Module ℂ Waves:= Packs_U.S.toModule
lemma K_norm (V:Waves): ‖V‖ ≤ max ‖V.1‖ ‖V.2‖:=le_rfl -- tune
-- Pack-accounted fees
lemma bean_G(V: Waves)(x:ℝ)(u:‖V‖≤x) : let F:= chartF V
 CostOle F ≤ x ∧ ‖(bF4 V).val‖≤x∧ ‖bF5 V‖ ≤x ∧ tautF (bm5 V).val ≤x:=by
 intro F; apply And.intro _ (And.intro _ (And.intro _ _))
 · apply le_trans _ u; apply max_le (le_max_left ..) (max_le _ _)
   · exact (le_max_right .. |>.trans (le_max_left .. |>.trans (le_max_right ..))) -- tune
   exact ((le_max_left ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))))
 · exact ((le_max_left ..).trans ((le_max_left ..).trans (le_max_right ..))).trans u
 · exact ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))).trans u
 exact ((le_max_right ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))).trans u
lemma bean_R(V:Waves)(x:ℝ)(F:CostOle (chartF V) ≤x)(a:‖(bF4 V).val‖≤x)(b:‖bF5 V‖≤x)(d:tautF (bm5 V).val≤x): ‖V‖≤x:=by
 let S:=chartF V
 exact max_le ((le_max_left ..).trans F) (max_le (max_le a ((le_max_left ..).trans ((le_max_right ..).trans F))) (max_le b (max_le ((le_max_right ..).trans ((le_max_right ..).trans F)) d)))
abbrev SectorVal := max (2500:ℝ) (max (mintPay (caboose *16)) ( (1/50:ℝ)⁻¹ * mintPay (caboose*16))) -- shouldn't include o M? defs
lemma well_Z(P:PressB p X Q h c)(s:0≤h)(e:o=X.val.1)(f:Waves)(u:MetaB o M f Q p h): ‖f‖ ≤ SectorVal*c:=by
 have hp:=skim P s; apply bean_R _ _
 · rw [u.port,e]; exact (winκ M P s).trans (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) hp)
 · rw [u.post,e]; exact (bill_G P s).trans (mul_le_mul_of_nonneg_right (le_max_left ..) hp)
 · rw [u.mast,e]; exact (bill_T P s).trans (mul_le_mul_of_nonneg_right (le_max_left ..) hp)
 rw [u.mixed,e]; exact (roof_T M P s).trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) hp)
end Layout
end Lenten
end YM.CF.TableF
end
