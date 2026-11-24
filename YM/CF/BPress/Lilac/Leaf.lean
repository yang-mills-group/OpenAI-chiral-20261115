import YM.CF.BPress.Peel.Script
import YM.CF.BPress.Mosaic.Music
/- Orientation pressure. Reference poses with same.* $¶Order.Root.Compare.s powers. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Lilac
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger
variable {m s N:Side}{B:BandWidth}{A:Bands (More N) B}{R:Hangar (More N)}
variable {H: Sugar.Crew A}{T:GramM N}{X: Sugar.Stage N}{Y:Driver N}
structure Born (A:Bands (More N) B)(R:Hangar (More N))(X:Sugar.Stage N)(Y: Driver N) :Prop where
 mat: Stamp A R X Y
 ideal(z:Fin 5): Licence (R:=R) (Reference z A) X.tile 0 ∅ (1:Micro (More N)) X.W X.q X.qX X.δ
 zeroG:0≤ Y.d
 posit:1 ≤ Y.j
variable (p:Born A R X Y)
open Bias Bias.Sails -- plane & ash
local notation "Xz" => fun z=> Reference z A -- tune notation
namespace Born
def H₁(z:Fin 5): Y.Pose:=Stage.player p.mat (p.ideal z) (guard0 p.zeroG)
lemma readK(z:Fin 5) : Y.decks.KG (p.H₁ z)= Rosetta z A X.W R X.tile 2:= player_KG (p.ideal z) p.mat (guard0 p.zeroG) -- tune
lemma readZ(z:Fin 5) : Y.decks.seat (p.H₁ z)= Picks A R ∅ := player_key (p.ideal z) p.mat (guard0 p.zeroG) -- tune
lemma heG(z:Fin 5) : (p.H₁ z).val.G=1:= rfl
lemma readF(z: Fin 5) : Y.decks.A (p.H₁ z)= nativeX Y.j Y.M N:= (nativeEq p.posit).symm
lemma readU(z:Fin 5): Y.decks.M (p.H₁ z)= 0 := by change Ts Y.F _ 1=0; simp [Ts,Kennel.capT,Spin.aim_zero] -- tune
local notation "V"=> Picks A R ∅

include p
lemma sees (z:Fin 5) : Cellar.Pass (Spin.Hole.pos V) (Spin.Hole.neg V) (loose V) (nativeX Y.j Y.M N) Y.ε ∧ Bore (netdark Y.j Y.M V) (coupling (Rosetta z A X.W R X.tile 2)) Y.v:=by
 let x:= p.H₁ z; let A1:=Y.decks.A; let t:=Y.decks.M; let T:=Y.decks.col; let T':=Y.decks.col'; let h:= (p.H₁ z).property.state; have he := (show Issued (Y.decks.keys true x) (Y.decks.keys false x) (A1 x) (t x) (T x) (T' x) Y.v Y.ε from h)
 let P:= he.rails; have hx:mood (A1 x) (t x)=nativeX Y.j Y.M N:=by rw [mood,show t x=0 from p.readU z,Spin.tiltT 1 he.proj]; exact p.readF z
 unfold Bias.netdark; rw [←hx,p.readK z|>.symm]; unfold Actor.keys at *; rw [show Y.decks.seat x= V from p.readZ z] at he P; have hl:shun (Single N) (Stride.Locks V true) (Stride.Locks V false)=loose V:=(plusMinus V).l0.symm; exact ⟨hl ▸ P, (show _ from (hl ▸ he.drum.backB))⟩ -- tune P type local notation V shadow A
abbrev tileF(z:Fin 5) := fareF Y.j Y.M V (Y.decks.KG (p.H₁ z))
lemma free_pay : p.tileF 0=0:= by unfold tileF; rw [p.readK 0]; exact Hazel.ash_0 A X.tile Y.M (p.ideal 0) (p.sees 0).1 p.posit (p.sees 0).2 -- tune
lemma real_b (z:Fin 5) : real_ (p.H₁ z)= Shale.oxide (Stride.Locks V true) (Stride.Locks V false) (nativeX Y.j Y.M N) 0 (coupling (Rosetta z A X.W R X.tile 2)):=by
 let K:=Y.decks; let A'(x):=Stride.Locks (K.seat (p.H₁ z)) x; unfold real_; rw [show K.keys true (p.H₁ z)=Stride.Locks V true from congrArg (fun S=>Stride.Locks S true) (p.readZ z),show K.keys false (p.H₁ z)=Stride.Locks V false from congrArg (fun S=>Stride.Locks S false) (p.readZ z), p.readF z,p.readU z]; rw [show K.col (p.H₁ z) 2= _ from congrArg Paint.coupling (p.readK z)]
lemma nonpos_t (z:Fin 5): p.tileF z ≤ 0:=by
 obtain ⟨v,t⟩:= p.sees z; unfold tileF; rw [p.readK, refFare (Rosetta z A X.W R X.tile 2) v]; have h:= Pf.Helm.below t.PSD (Pf.Issued.normL t); exact ((smul_le_smul_of_nonneg_left h (by norm_num : (0:ℝ)≤1/4)).trans (smul_nonpos_of_nonneg_of_nonpos (by norm_num) (neg_nonpos.mpr t.PSD))) -- tune psd property not inequality
end Born
end YM.CF.BPress.Lilac
