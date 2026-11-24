import ForceSatin.Picket
import ForceSatin.Blush
import ForceSatin.Loge
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip

-- uniform scalar exponents charges
open _root_.YM.Next.Rank.Spindle
open Gentle.Solace Rail
open _root_.YM.Regis.Resonance Lull
open Fineness
namespace Moon
open ProbabilityTheory
open Lifted Afterglow Satin Cygnet Loaves Horizons InnerProductSpace
open _root_.YM.Regis.Head
section
variable {per cut:ℕ→ℕ} {Hr:Real.exp 1≤ P.x} {I E}(u:Universal Y Hr per cut I E) {A D:ℕ→ℕ} {G}(p:Tower.Coherent Y Hr (i:=per) (k:=cut) (E:=E) G A D)
variable {v:ℕ→ℕ}(hp:Tendsto v atTop atTop)
local notation "U₀" => per ∘ A ∘ v
local notation "D₀" => cut ∘ D ∘ v
local notation "Rꜰ"=> P.R.L
include p u hp
variable {W0 βm} (H:Picker Y (per ∘ A ∘ v) (cut ∘ D ∘ v) W0 βm)
variable (s:ℕ){y:ℝ}
include H
open Regis.Head.Brecht Regis.Circuit Regis.Circuit.SpringDay Spring
abbrev gateL (s i k:ℕ) := P.V.L.H (Y.uv k-s)
abbrev gateW(s i k:ℕ):=rimble (More (count Y s i)) (gateL Y s i k)
omit p u hp H in
lemma checks(i k:ℕ)(x y:Cover)(F D:PlaqAxes)(I J: SU.group.ColorIndex): (↑(pairP (Sun (P.V.L.mood (Y.uv k-s)) (P.V.L.tied (Y.uv k-s)) 1 ∘ DirN (count Y s i)) ((x,F),I) ((y,D),J)):ℂ) = (sch (G:=SU.group) I J :ℂ)*gateW Y s i k (wrap _ (x-y), Exterior.plaquette F) (0, Exterior.plaquette D) :=by
 let N:= count Y s i; let w:=More N; let R:=P.V.L.roof (Y.uv k-s); have hh:Even w.val:= by exact ⟨N.val,by change N.val *2=N.val+N.val; omega⟩
 have ht:=crest_pledge (P.V.L.mood (Y.uv k-s)) (P.V.L.tied (Y.uv k-s)) (R.2.1 w) R.1 P.K.width (DirN N ((x,F),I)) (DirN N ((y,D),J)) hh; refine ht.trans ?_; unfold gateW; apply congrArg ((sch (G:=SU.group) I J :ℂ)*·); change rimble w _ (wrap w x,Exterior.plaquette F) (wrap w y,Exterior.plaquette D) = _; rw [moonstone,show (0:Site w)= wrap w 0 from (map_zero _).symm,moonstone,sub_zero]
lemma eastCo : Tendsto (fun i:ℕ=> (count Y s (U₀ i)).val) atTop atTop := (count_grows Y s).comp ((u.pick.grow_i.comp p.growsA).tendsto_atTop.comp hp)
local instance : Nonempty SU.group.ColorIndex := YM.Stationary.colorAvail SU.group Thera.yet_one
noncomputable def wObj (W:HorizonLens→ HorizonLens→ℝ)(F D: PlaqAxes)(x:Cover):ℂ := (W ((x,F),Classical.arbitrary SU.group.ColorIndex) ((0,D),Classical.arbitrary SU.group.ColorIndex):ℂ)
lemma songOfSongs (F D:PlaqAxes)(x:Cover): Tendsto (fun i=>gateW Y s (U₀ i) (D₀ i) (wrap _ x, Exterior.plaquette F) (0, Exterior.plaquette D)) atTop (𝓝 (wObj (W0 s) F D x)):=by
 let I:= Classical.arbitrary SU.group.ColorIndex; let u0:= ((x,F),I); let u1:= (((0:Cover),D),I); apply (Complex.continuous_ofReal.continuousAt.tendsto.comp (H.cost s u0 u1)).congr; intro i; simp only [Function.comp_apply]; exact (checks Y s (U₀ i) (D₀ i) x 0 F D I I).trans (by simp [Regis.Head.Brecht.sch])  -- tune include flags
lemma lagoon (F D:PlaqAxes)(x y:Cover)(I J:SU.group.ColorIndex) : (↑(W0 s ((x,F),I) ((y,D),J)) :ℂ)= (sch (G:=SU.group) I J:ℂ)*wObj (W0 s) F D (x-y) := tendsto_nhds_unique ((Complex.continuous_ofReal.continuousAt.tendsto.comp (H.cost s ((x,F),I) ((y,D),J))).congr fun i=> checks Y _ _ _ x y F D I J) ((songOfSongs Y u p hp H _ F D _).const_mul _)
lemma worx(F D:PlaqAxes)(l: List Cover): ∃ C:ℝ,0<C∧∀ s x, x≠0→ ‖muJet l (wObj (W0 s) F D) x-muJet l (specter F D ∘ scape) x‖ ≤ C/rally x^(5+l.length):=by
 obtain ⟨C,c,S⟩:=asteroid P.K.width (zero_lt_one.trans_le P.V.up) P.K.top.clip P.V.W.parcel F D l; refine ⟨C,c,fun s x a=>?_⟩
 let y(i):=(U₀ i); let V(i):= D₀ i; let W(i:ℕ):=count Y s (y i); let Q(i:ℕ):=gateL Y s (y i) (V i); let x'(i):=Y.uv (V i)-s; let M(i):= P.V.L.roof (x' i); let h(i:ℕ):=More (W i)
 have ht:Tendsto (fun i=> (h i).val) atTop atTop:=tendsto_atTop_mono (f:=fun i=>(W i).val) (fun i=> by change (W i).val ≤ (W i).val *2; omega) (eastCo Y u p hp H s)
 apply le_of_tendsto ((((muJet_go l (songOfSongs Y u p hp H s F D) x).sub_const _)).norm)
 exact S h Q ht (fun i=> (M i).2.1 _) (fun i=> (M i).1) (fun i=>⟨(W i).val, by change (W i).val *2=(W i).val+(W i).val; omega⟩) x a
lemma sagaChar : ∃ A:ℕ, CompassChar (fun i=> count Y s (U₀ (A+i))) (fun i=>(gram Y s (U₀ (A+i)) (D₀ (A+i))).J.M):=by
 obtain ⟨z,h⟩:= Picker.kings Y u p hp H s; obtain ⟨A,a⟩:= eventually_atTop.1 h; have e:Tendsto (fun i:ℕ=> A+i) atTop atTop:=tendsto_atTop_mono (fun i=> show i≤ (A:ℕ)+i from (by omega)) tendsto_id
 have V:Tendsto (fun i:ℕ=> (gram Y s (U₀ i) (D₀ i)).J.M.val.val) atTop atTop:=by refine tendsto_atTop.mpr fun n=> ?_; filter_upwards [(((u.pick.grow_k.comp p.growsB).tendsto_atTop.comp hp)|>.eventually (tide_joint Y s n))] with i a; exact a _
 exact ⟨A,fun i=> Vale.val_e ..,(eastCo Y u p hp H s).comp e, V.comp e,fun i=> (a (A+i) (by omega)).1⟩
#print axioms checks
#print axioms worx
#print axioms sagaChar
#print axioms lagoon
end
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
