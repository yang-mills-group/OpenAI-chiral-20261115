import YM.SU5.Assay.SeenBox
import YM.SU5.Assay.Vintage
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j
open SlabMark.Etch
variable (P j)
variable {S:Finset Cover}
local notation "i₀"=> P.projection.rows
local notation "k₀"=> P.projection.columns
local notation "p₀"=> P.period
local notation "q₀"=> P.cutoff
local notation "T"=> enclave P.calibration

lemma constantPremiere {z:Cover}{d:ℝ}(hw:0<w)(hd:0≤d)(hz:z j=0)
    (v:House K w z 0 S)(t:InTest K true S false f.val)
    (y:Premiere (i:=p₀) (k:=q₀) (a:=i₀) (b:=k₀) Y H s w z (fun _=> f.val) d):
    ‖P.meanBox j s w f‖ ≤ d:=by
 have p:P.BEntry j w f:=⟨hw,S,t,entryHouse Y H j w z hz v⟩
 rw [meanBox_eq s p]
 obtain ⟨x,g⟩:=valuation Y H t
 have ht:=BQueue.stay t (lt_of_lt_of_le (by norm_num: (0:ℝ)<1) (le_max_right x _))
    (fun i j=> (g i j).trans (le_max_left _ 1))
 refine premiereBox Y H V s π j w z hw hz _ v π Qt false C₀ (p.card s) ht d hd ?_
 intro q e
 filter_upwards [y] with i YY
 intro l h n a b' F g
 exact le_trans (YY l h n a b' F g) (pow_le_pow_left₀ hd e.le _)

open Papyrus
namespace Tasting
/-- Supplemental qualifications for tag and flash residual. -/
def Paid (Λ₀:Preparation):Prop:=
 Geometry Λ₀ ∧ (∃ R:ℝ,Franc.postage Λ₀.K.j R∧0≤R∧ Franc.charge R≤ Λ₀.h) ∧
 (∃ δ:ℝ,Λ₀.d ≤δ ∧ ∃ N:ℕ,∀ η>(0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N≤n.val→
    CF.Pannier.Chancel.Winter Λ₀.K.j δ n γ w η) ∧
 (∀ᶠ n:ℕ in atTop,∀ N:Side,n≤N.val→∀ M:Tulip.Male, Franc.Meshy.Muster Λ₀.d N M)
end Tasting

variable {P}
noncomputable def tasteTest (f:P.Test)(y z:ℂ): P.Test:=1+z • (f+(-y)•1)
lemma tasteTest_bay (p:f∈bay K S true)(y z:ℂ): tasteTest f y z∈bay K S true:=by
 let A:=bay K S true; exact A.add_mem A.one_mem (A.smul_mem (A.add_mem p (A.smul_mem A.one_mem _)) _)
lemma tasteTest_color (p:f∈T)(y z:ℂ): tasteTest f y z∈T:=(T).add_mem (T).one_mem ((T).smul_mem ((T).add_mem p ((T).smul_mem (T).one_mem _)) _)

variable (P)
/-- Arbitrarily fine footprint, with resolution-independent test coefficients and
 width in ticks once z and margin are chosen. Control in the preselection norm. -/
def Taste (f:P.Test)(S:Finset Cover)(y:ℂ):Prop:=
 ∀ j:Axis,∀ ε> (0:ℝ), ∃ ζ> (0:ℝ), ∀ z:ℂ, 0<‖z‖ → ‖z‖≤ζ → ∃ d> (0:ℕ), P.BFits d S ∧
  ∀ᶠ s:ℕ in atTop,
   ‖P.meanBox j s (d+d) (P.shifts j d (tasteTest f y z))‖ ≤ Real.exp (3*(ε*‖z‖))


open Tasting
open CF.Papyrus.Franc.Loaves

lemma hasTaste (p:Paid P.par)(v:S.Nonempty)(u:f∈bay K S false)(t:f∈T): ∃ y,P.Taste f S y:=by
 obtain ⟨g,⟨R,h,q,d⟩,⟨δ,m,e⟩,ht⟩:=p
 have u':InTest K false S false f.val:=u; have t':CovCover K f.val:=t
 obtain ⟨L0,a,X⟩:=recipe u'
 rw [X] at u' t'
 refine ⟨tallyW L0,?_⟩; intro j ε hε
 obtain ⟨ζ,x,o⟩:=Papal.vintageG Y H g v hε a u' t' h q d m e ht j
 refine ⟨ζ,x,?_⟩; intro z p x
 obtain ⟨W,w,y,H',G,F⟩:=o z p x; let D:= tasteTest f (tallyW L0) z
 refine ⟨w,H',fun i x h=>G i x (y h),?_⟩
 have hf:D.val=Papal.fiz K z L0:=by
    change 1+z•(f.val+(-(tallyW L0))•1)=1+z•(dek K L0+(-(tallyW L0))•1); rw [X]
 have b':D∈bay K W true:=tasteTest_bay (tallerBay K S true y (widerBay K S false u)) _ _
 filter_upwards [F] with s hs
 obtain ⟨n,E⟩:=hs
 apply P.constantPremiere j (add_pos H' H') (Real.exp_pos _).le (z:=Papal.coSeat j w) (by simp [Papal.coSeat]) (Papal.seated Y H w j W G)
 · exact P.shifts_support _ _ _ b'
 have ep:Tendsto (fun i=>p₀ (i₀ i)) atTop atTop:= ((V).pick.grow_i.comp (π).growsA).tendsto_atTop
 have eq:Tendsto (fun i=>q₀ (k₀ i)) atTop atTop:= ((V).pick.grow_k.comp (π).growsB).tendsto_atTop
 filter_upwards [ep.eventually E,eq.eventually_ge_atTop n,(π).finance s] with i e t v
 change Mosaic _ _ _ (relocate _ _ _ D.val) _ _
 rw [hf]; exact e _ t v

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.hasTaste
