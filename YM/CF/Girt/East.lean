import YM.CF.Girt.Zero
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Girt
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
local notation "G₀"=> SU.group
variable {f n :Side}{CΛ δ v a P h d μ ε w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
lemma pompK(X Y:Type*)[LinearOrder X][Fintype X][LinearOrder Y][Fintype Y](U:X≃Y)(A:Op X)(v:Wave X): effectK (portW U A) (cartsL U v)=cartsL U (effectK A v):=by rw [← flexL]; exact (freezes _ _ (shelfG ..) _ _).symm -- direction
lemma mastC(t:Seat n→ E): effectK (tradew n t).val (mateK n)=mateK n:=by
 let h:=t ∘ node (N:=n); let A:=conjG matter h
 have he: portW (Tulip.helix n).symm A.val=(tradew n t).val:=by
    unfold portW A; ext ⟨⟨i,b⟩,v⟩ ⟨⟨j,c⟩,k⟩; by_cases h:i=j<;>by_cases e:b=c<;> simp [h,e,conjG,tradew,jump_apply, Tulip.helix, Lat.color] <;> first| rfl|simp
 rw [← he,mateK,pompK]; rw [show effectK A.val (linearB n)=_ from ref_frame h]
lemma score_m (G:Ratio n f)(M:Male)(X:Nom n f)(sN:ℕ)(Y: Tax L (ticketT (Thread j) true) false true a v sN d)(p:G.count=L)(w:sN≤n.val) -- need nat distinct minim
 (h:unionP X∈legal G d)(g:Seat f→ E)(r:∀ i:Seat n,g ((ratio G).embed i)=1) (V:Phys f):fire (Thread j) G M (unionP (july G g X)) (cartsL (switchG G).symm (effectK (tradew f g).val V))= fire (Thread j) G M (unionP X) (cartsL (switchG G).symm V):=by
 let U:= (Peaks.parcel G true d).run g; let W:=ticketT (Thread j) true M G; let A:= unionP X; let B:=unionP (july G g X)
 have hs: W B*U.val=W A:=by
    rw [show W B= _ from crown_pulse G (Y _ _ p w) X h g]
    have hp: ((Peaks.parcel G false d).run g).val=1:=by
      rw [warrant]; change jump (Equiv.refl (Inta G)) (fun i=> (matter (g ((ratio G).embed (node i.1)))).val)=_; simp_rw [r,map_one, show (1:UNI SU.Slot).val=(1:Op SU.Slot) from rfl,jump_id]
    rw [hp,one_mul,mul_assoc,U.property.1,mul_one]
 have hx(v: Phys f) : effectK (W B) (cartsL (switchG G).symm (effectK (tradew f g).val v))=effectK (W A) (cartsL (switchG G).symm v):=by
    rw [←pompK]; change acts _ (acts (quant U.val) _)=acts _ _; rw [←act_mul,←quant_mul,hs]
 have hm:chargeA (Thread j) G M B=chargeA (Thread j) G M A:=by
    unfold chargeA skyGlow; have hl:= hx (mateK f); rw [mastC] at hl; exact congrArg (inner ℂ (oceanA G)) hl
 unfold fire; change ( (sect0 G*chargeA _ G M B)⁻¹) • pailL _ _ _= _; rw [hm,hx V]
end YM.CF.Girt
