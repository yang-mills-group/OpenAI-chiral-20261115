import YM.SU5.FiniteGaugeData.Stent.Velcro
import YM.SU5.FiniteGaugeData.Indigo.Pilip
import YM.SU5.FiniteGaugeData.LapisQ.Figura
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
namespace Succulent
open Strata
variable (R:Patch)
namespace SpineV
variable (q:Cover)(F:LinksC)
local notation "a₁"=> negDir 0
local notation "b₁"=> negDir 1
abbrev Nest:= YM.SU5.FiniteGaugeData.LapisQ.Nosh.leg0
local notation "η"=>nodeC (specialM R.L)
-- swap [b₁,a₁] to [a₁,b₁]
local notation "κu"=> travel F 0
local notation "Pu" x:max=> travel F x
lemma lowerDiff(x:Cover): stop x [a₁,b₁]=stop x [b₁,a₁]:=by simp only [stop]; abel
lemma bee_face(x:Cover): faceValue F (stop x [a₁,b₁],Nest)=(travel F x [b₁,a₁])⁻¹*travel F x [a₁,b₁]:=by
 let p:= [a₁,b₁]; let r:=[b₁,a₁]; let y:= stop x p; let W:=square 0 1; change travel F y W= _; rw [show W= Lattice.reverse [b₁,a₁]++[a₁,b₁] from rfl, travel_append]; -- transport second cancels? reverse ba = [+a,+b], yes
 rw [show y=stop x [b₁,a₁] from lowerDiff x, reverse_stop,travel_reverse] -- `lower` F omitted remove.
abbrev entryW(U:LinksC)(p:RG.Slot): SU.E:= travel U 0 p.walk * faceValue U (p.offset,p.plaq)*(travel U 0 p.walk)⁻¹
abbrev crew (P:Walk):RG.Slot:= ⟨P++[a₁,b₁],Nest⟩
local notation "V₉" p:max=> travel F 0 p
lemma before (P S: Walk): entryW F (crew P)= travel F 0 (P++ [a₁,b₁]++S)*(travel F 0 (P++ [b₁,a₁]++S))⁻¹:=by
 -- lists append right assoc.Ver
 unfold entryW crew RG.Slot.offset; simp only [travel_append, stop_append]; rw [bee_face, lowerDiff]; group -- check group tactic
abbrev T₁:Walk:= [a₁,b₁,a₁,b₁]
abbrev T₂:Walk:= [b₁,a₁,a₁,b₁]
abbrev T₃:Walk:= [b₁,a₁,b₁,a₁]
noncomputable abbrev lyre : Fin 4→RG.Slot := ![crew [a₁], crew [], crew [b₁,a₁], crew [b₁]]
noncomputable abbrev sealX (U:LinksC) : List SU.E:=[entryW U (lyre 0),entryW U (lyre 1),entryW U (lyre 2),entryW U (lyre 3)]
local notation "E₈" p:max=> entryW F p
lemma hopes : (sealX F).prod = κu dogwalk * (κu birdwalk)⁻¹:=by
 have h₁:E₈ (lyre 0)= κu dogwalk *(κu T₁)⁻¹:= before F [a₁] [b₁]; have h₂:E₈ (lyre 1)= κu T₁ *(κu T₂)⁻¹:= before F [] [a₁,b₁]; have h₃:E₈ (lyre 2)= κu T₂* (κu T₃)⁻¹:= before F [b₁,a₁] []; have h₄:E₈ (lyre 3)= κu T₃*(κu birdwalk)⁻¹:= before F [b₁] [a₁]; unfold sealX; simp only [List.prod_cons,List.prod_nil,h₁,h₂,h₃,h₄]; group
lemma translateH (p x:Cover)(u:Walk): travel (Lattice.translate p F) x u= travel F (x+p) u:=by rw [← Lattice.pull_one, travel_pull]; simp [Lattice.affine]
abbrev amulet (R:Patch)(U:LinksC): LinksC:= Lattice.translate (nodeC (specialM R.L)) U
lemma datum : SpanM R F= (sealX (amulet R F)).prod:=by unfold amulet; rw [hopes,translateH,translateH,zero_add]
open CF.Indigo
lemma melodyP (p : RG.Slot) : SU.group.curvature (entryW F p) = p.eval (G:=SU.group) F:= SU.group.curvature_conjugate ..
lemma chordP (p:RG.Slot): SU.group.chord (entryW (amulet R F) p)=SU.group.chord (faceValue F (p.offset+η,p.plaq)):=by unfold entryW; rw [SU.group.chord_conj]; unfold faceValue; unfold amulet; rw [translateH] -- tune
-- catalyst trajectory
abbrev Obl(x:Fin 4→SU.group.Color):=x 0+ (x 1+(x 2+x 3))
noncomputable abbrev Cy(U:LinksC):= Obl (fun i=> (lyre i).eval (G:=SU.group) (amulet R U))
lemma lumen : Cy R F= choirQ (sealX (amulet R F)):=by unfold choirQ sealX; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil, add_zero,melodyP] -- tune
abbrev testV (x:Cover)(p:RG.Slot) : Face ℤ:= (p.offset+x,p.plaq)
noncomputable abbrev cradle (R:Patch): Finset (Face ℤ):=univ.image fun i=>testV (nodeC (specialM R.L)) (lyre i)
lemma pallor(t:ℝ)(p:¬alarm (cradle R) t (F,F)) : shades (sealX (amulet R F)) t:=by
 have h(i:Fin 4): SU.group.chord (entryW (amulet R F) (lyre i)) ≤ t:=by rw [chordP]; exact le_of_not_gt (fun u=>p ⟨testV _ (lyre i),mem_image_of_mem _ (mem_univ _),u⟩)
 intro u U; rcases List.mem_cons.mp U with rfl|U; exact h 0; rcases List.mem_cons.mp U with rfl|U; exact h 1; rcases List.mem_cons.mp U with rfl|U; exact h 2; rw [List.mem_singleton.mp U]; exact h 3
-- Combined.Er
variable {t C:ℝ}
include R
lemma care_U : ∃ D:ℝ,0<D ∧∀ i:LinksC,∀ t:ℝ, ¬alarm (cradle R) t (i,i) → ‖Nylon R i-1‖≤ D*t^2:= by
 obtain ⟨D,t,hD⟩:= cardigan_U; refine ⟨16*D,by positivity,fun U s y=>?_⟩; let E:= SpanM R U; have hx:SU.group.chord E≤ 4*s:=by rw [show E=_ from datum R U]; exact chordD (pallor R U s y)
 rw [officials]; exact (hD _).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (SU.group.chord_nonneg _) hx 2) t.le).trans_eq (by ring))
lemma curr_B (U: LinksC)(p:¬alarm (cradle R) t (U,U)): ‖Cy R U‖ ≤ 4*t:=by rw [lumen]; exact normD (pallor R U _ p) -- defeq casts likely fails
lemma hood_B (e:0<C) : ∃ T:ℝ, 0<T ∧∀ U:LinksC,∀ t:ℝ, 0≤t→t≤ T→¬alarm (cradle R) t (U,U)→ ‖Nylon R U-1+(↑(colorG*‖Cy R U‖^2):ℂ)‖ ≤ C*t^2:=by
 obtain ⟨U,u,p⟩:= CF.Indigo.tutelary 4 e; refine ⟨U,u,fun x t p' a h=> ?_⟩; rw [officials,lumen,datum]; exact p (sealX (amulet R x)) (Nat.le_refl 4) t p' a (pallor R x _ h)
#print axioms hood_B
#print axioms hopes
end SpineV
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
