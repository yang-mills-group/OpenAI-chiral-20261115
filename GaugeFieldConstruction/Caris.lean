import GaugeFieldConstruction.Gisborne
import GaugeFieldConstruction.Enmity
import GaugeFieldConstruction.Quail
import YM.CF.Roots.East
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
variable {N:Side}{h t b a:ℝ}{I:Type}[LinearOrder I][Fintype I]
open Py.Riant -- remove
variable (p:BudgetPoint) (v:0 ≤ h)
-- full Shape Pay Readers
abbrev SecX (p:BudgetPoint) (v:0 ≤ h)(N:Side) : Cornea (Scree.Hub N) (Pane N) (Cipher N) (More N) where
 Φ x:= x.val.2
 valid:=fun _ _=>True
 Lux i z b:= PressB p i z h b
 posG := fun x _ _ t=>Roots.gradeE x _ t v
 zero:=fun i x t=>by rw [show x=0 from funext fun y=>t _ trivial]; exact Vale.rinse ..
 add i _ _ _ _ f g:= prop_add _ i f g
 coin i _ _ q z:= Floral.regular_scale z q
 widen i _ _ _ f z:= TableF.Lenten.Layout.lift_PV f z
 inert i _ _ Q _ h:= by rw [←funext (fun i=>Q i trivial)]; exact h
abbrev SecK (p:BudgetPoint) (v:0 ≤ h)(N:Side): Cornea (Scree.Force N) (Orbit N) (Cipher N) (More N) where
 Φ x:=x.val.1.val.2
 valid:=fun _ _=>True
 Lux i z b:= ForceB p i z h b
 posG:=fun i _ _ t=> Roots.gradeQ i _ t v
 zero:=fun i x t=>by rw [show x=0 from funext fun y=> t _ trivial]; exact Vale.rinsed ..
 add i _ _ _ _ f g:= Roots.dom_h i _ _ f g
 coin i _ _ q z:= Roots.dúe i _ q z
 widen i _ _ _ f z:= Floral.force_incr f z
 inert i _ _ Q _ h:= by rw [←funext (fun i=>Q i trivial)]; exact h
abbrev SecW (p:BudgetPoint)(v:0 ≤ h)(N:Side): Cornea (Aura N) (Orbit N) (Cipher N) (More N) where
 Φ i:= i.val
 valid:=fun _ _=>True
 Lux i z b:= Medal p i.val ∅ z h b
 posG:=fun i _ _ t=>Medal.wage t v
 zero:=fun i x t=>by rw [show x=0 from funext fun y=> t _ trivial]; exact Medal.zeroT
 add:=fun _ _ _ _ _ h t=> Medal.plus h t
 coin:=fun _ _ _ q z=> Floral.medal_scale z q
 widen:=fun _ _ _ _ f g=> Medal.big f g
 inert i _ _ Q _ h:=by rw [←funext (fun i=> Q i trivial)]; exact h
abbrev ΘV (D K:Support (More N)):Prop:=D.Nonempty ∧ D ⊆ K
abbrev SecQ (p:BudgetPoint)(h:ℝ)(N:Side): Cornea (Aura N) (Support (More N) × Orbit N) (Cipher N) (More N) where
 Φ i:=i.val
 valid i x:= ΘV x.1 i.val
 Lux i z b:= 0≤b ∧∀ X:Support (More N), ΘV X i.val  →  Medal p i.val X (fun x=>z (X,x)) h b
 posG:=fun _ _ _ t=> t.1
 zero:=fun i x t=> ⟨le_rfl,fun D h=>by rw [show (fun u=>x (D,u))= 0 from funext fun k=> t _ h]; exact Medal.zeroT⟩
 add:= fun _ _ _ _ _ h t=> ⟨add_nonneg h.1 t.1,fun u p=> Medal.plus (h.2 u p) (t.2 u p)⟩
 coin:= fun _ _ _ h z =>⟨mul_nonneg (norm_nonneg _) h.1,fun i p=>Floral.medal_scale z (h.2 i p)⟩
 widen:= fun _ _ _ _ h t=> ⟨h.1.trans t,fun i p=> (h.2 i p).big t⟩
 inert:=fun i g h t r p=> ⟨p.1,fun u v=> by rw [←show (fun x=>g (u,x))=(fun x=>h (u,x)) from funext fun x=>t (u,x) v]; exact p.2 u v⟩
-- formula through Dot grades. 
abbrev expertK {Z:Type}(Φ:Z →  Support (More N))(i:Z)(p:BudgetPoint)(a:ℝ)(k:Seat N):ℝ:= if k∈ Φ i then dra_k p.B a (Φ i) else 0
abbrev κK (N:Side)(p:BudgetPoint)(a:ℝ): Scree.Hub N → Seat N → ℝ:= fun i x=> expertK (fun i:Scree.Hub N=> i.val.2) i p a x
lemma Fbank (F:RegBudget N): ForgeB F (κK N p a) p h (fun _=>b)↔ ShelfK (SecX p v N) F p.B a b:=by
 constructor
 · rintro ⟨C,h,f⟩; refine ⟨C,h,fun x =>le_trans (le_of_eq ?_) (f x)⟩; change ∑ j∈ _, _ = _; unfold κK expertK; simp_rw [ite_mul,zero_mul,←sum_filter]
 rintro ⟨C,h,f⟩; refine ⟨⟨C,h,fun x=>le_trans (le_of_eq ?_) (f x)⟩⟩; unfold κK expertK; simp_rw [ite_mul,zero_mul,←sum_filter]
lemma Kbank (F:ForceBudget N): SanB F (giftK p a) p h (fun _=>b) ↔ ShelfK (SecK p v N) F p.B a b:=by
 constructor
 · rintro ⟨C,h,f⟩; refine ⟨C,h,fun x=>le_trans (le_of_eq ?_) (f x)⟩; unfold giftK; simp_rw [ite_mul,zero_mul,←sum_filter]; rfl
 rintro ⟨C,h,f⟩; refine ⟨⟨C,h,fun x=>le_trans (le_of_eq ?_) (f x)⟩⟩; unfold giftK; simp_rw [ite_mul,zero_mul,←sum_filter]; rfl
lemma Wbank (F:Vow.Pax N): (∃ A, (∀ i:Aura N, Medal p i.val ∅ (F i) h (A i))∧∀ j:Seat N,tallB A p.B a j≤ b) ↔ ShelfK (SecW p v N) F p.B a b:=by
 constructor
 · rintro ⟨C,h,f⟩; refine ⟨C,h,fun x =>le_trans (le_of_eq ?_) (f x)⟩; unfold tallB; exact sum_congr rfl fun i _=>mul_comm ..
 rintro ⟨C,h,f⟩; refine ⟨C,h,fun x=>le_trans (le_of_eq ?_) (f x)⟩; unfold tallB; exact sum_congr rfl fun i _=>mul_comm ..
abbrev FlatQ (F:Vow.Cusp N)(i:Aura N)(u:Support (More N) × Orbit N):Cipher N:= F i u.1 u.2
lemma Qbank (h:ℝ)(F:Vow.Cusp N): (∃ A,Anuk F A p h ∧∀ j:Seat N,tallB A p.B a j≤b)↔ ShelfK (SecQ p h N) (FlatQ F) p.B a b:=by
 constructor
 · rintro ⟨C,h,f⟩; refine ⟨C,fun i=> ⟨h.1 i,fun u t=>h.2 i u t.1 t.2⟩,fun x=>le_trans (le_of_eq ?_) (f x)⟩; unfold tallB; exact sum_congr rfl fun i _=>mul_comm ..
 rintro ⟨C,h,f⟩; refine ⟨C, ⟨fun i=>(h i).1,fun i T v s=>(h i).2 T ⟨v,s⟩⟩,fun x=>le_trans (le_of_eq ?_) (f x)⟩; unfold tallB; exact sum_congr rfl fun i _=>mul_comm ..
variable (U:Key I →  RegBudget N)(V:Key I → ForceBudget N)
lemma RegT_p (g:∀ i x,River (fun z=>U z i x))(y:0<h)(w:∀ z∈hill I, ShelfK (SecX p v N) (U z) p.B a b) (l:List I): ShelfK (SecX p v N) (fun i y=> tipI (fun z=>U z i y) l) p.B a b:=by
 apply (Fbank ..).mp
 apply onset_t U y (κK N p a) _ _ _ (fun i x=> (Fbank p v (a:=a) _).mpr (w i x)) g l
 · intro i j; unfold κK expertK; split; exact (Real.exp_pos _).le; exact le_rfl
 intro i; refine ⟨i.val.1,?_⟩; unfold κK expertK; rw [if_pos i.property]; exact Real.exp_pos _
lemma ForceT_p (g:∀ i x,River (fun z=> V z i x))(y:0<h)(w:∀ z∈hill I,ShelfK (SecK p v N) (V z) p.B a b) (l:List I):ShelfK (SecK p v N) (fun i y=>tipI (fun z=> V z i y) l) p.B a b:=by
 apply (Kbank ..).mp
 apply insight_t V y (giftK p a) _ _ _ (fun i x=> (Kbank p v _).mpr (w i x)) g l
 · intro i j; unfold giftK; split; exact (Real.exp_pos _).le; exact le_rfl
 intro i; refine ⟨i.val.1.val.1,?_⟩; unfold giftK; rw [if_pos i.val.1.property]; exact Real.exp_pos _
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
