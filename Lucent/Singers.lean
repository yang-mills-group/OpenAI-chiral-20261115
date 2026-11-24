import Lucent.LatticeFieldEstimates
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

set_option maxHeartbeats 380000
set_option linter.unusedSimpArgs false
open YM.Stationary (Gaia)
open Onyx Kea Flare Dial Ballad.Twah Cordial Emu Gist
open Regis Circuit
variable {I:Type}(Y:I→Role)
namespace Arity

open Stencil Hiro
open Lamour.Bridge.Celeste
variable (N:Side)(W:I→Staff)(C:I → ColorL)(g:Seat N→SU.E)(U:Fields N)
    (i k u v:I)(z:Window.Family)(F:List (Tint I))(X:Op Slot)
lemma rbeads :
 dream N W (beaded F i X) C=
 glint (hues C) F •(∑ a,∑ b, X a b • cell N (seat W i) (body W i) a b):=by
 simp only [dream,beaded,pack_q,scale_q,mono_q,knit,spind,weave,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,smul_sum]
 exact sum_congr rfl fun _ _=>sum_congr rfl fun _ _=>smul_comm _ _ _

lemma d_beats :
 dream N W (D z k) C= SitSpin.raw (seat W k) z (body W k).1 (body W k).2 N U:=by
 unfold D; rw [rbeads,glint_nil,one_smul,metals]
 have h(a): (∑ b,(cutM (Window.colors z)) a b •cell N (seat W k) (body W k) a b)=if a∈colors z then cell N (seat W k) (body W k) a a else 0:=by
   simp [cutM, Matrix.diagonal_apply,ite_smul,sum_ite_eq]
 simp_rw [h]; rw [←sum_filter]; simp [SitSpin.raw,cell]
lemma d_sings : Singing W (D z k):=by
 intro N C g; let f:=U0 N
 rw [d_beats N W _ (simultaneous g f), d_beats N W _ f]
 exact (SitSpin.voice ..).2 N g f
where U0 (N:Side):Fields N:= (1,1)

lemma v_beats :
 dream N W (V i) C=wrapCurrent (seat W i) (body W i) 1 N (C i):=by
 nth_rw 1 [show C i=∑ b:Pig, (C i b) • mug b from (mug.sum_repr (C i)).symm.trans (Finset.sum_congr rfl fun b _=> congrArg (· • mug b) (show (mug.repr (C i)) b = C i b from mug_eq (C i) b))] -- lhs C i not explicit thus first
 unfold dream V; rw [pack_q,map_sum]; refine sum_congr rfl fun p _=>?_
 rw [map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ),hold_sum]
 change dream N W (beaded _ i (crest p)) C=_; rw [rbeads,glint_cons,glint_nil,mul_one]
 refine congrArg _ (sum_congr rfl fun b _=>sum_congr rfl fun c _=>?_); 
 let a:=create (basisC N (seat W i) (upSpin (body W i).1) b)
 let z:=Fock.remove (basisC N (seat W i) (dnSpin (body W i).2) c)
 change crest p b c • (a*z) = crest p b c • (Twah.gold 1 • (z*a))
 rw [show z*a= -(a*z) from SitSpin.cr_swap _ _ _ _ _ _]; simp [Twah.gold]
lemma v_sings : Singing W (V i):=by
 intro N C g; rw [v_beats,v_beats]
 exact current_cov (seat W i) (body W i) 1 (C i) (1,1) g
#check @Gauge.adjoint
#check @LinearIsometry.inner_map_map
#check EuclideanSpace.inner_eq_star_dotProduct

lemma g_beats :
 dream N W (G u v) C=(↑(inner ℝ (C u) (C v)):ℂ) • 1:=by
 simp only [dream,G,pack_q,mono_q,knit,spind,weave,List.map_nil,List.prod_nil,glint_cons,glint_nil,mul_one, ← sum_smul]
 rw [real_inner_comm,EuclideanSpace.inner_eq_star_dotProduct]
 simp [dotProduct, hues]
lemma sing_mul (W:I→Staff)(S T:Stencil I)(h:Singing W S)(k:Singing W T): Singing W (S*T):=by
 intro N G g; rw [dream_mul,h,k,dream_mul,map_mul]

lemma g_sings (h:(W u).u=(W v).u): Singing W (G u v):=by
 intro N C g; rw [g_beats,g_beats,twist_scalar,map_one]; unfold crown
 rw [show (W v).scope N=(W u).scope N from congrArg (fun x=>wrap (More N) (nodeC x)) h.symm]
 let H:SU.group.Color →ₗᵢ[ℝ] SU.group.Color:={ SU.group.adjoint (g ((W u).scope N)) with norm_map' := SU.group.norm_adjoint _}
 exact congrArg (fun a:ℝ=>(a:ℂ) • (1:FC (Single N))) (H.inner_map_map (C u) (C v))
open Papal
lemma v_returns (b:ℕ)(ρ t:ℝ): kite b ρ t W (V i)=(W i).rungWeave ρ b t:=by
 funext n x; unfold kite; rw [v_beats,Staff.onMark];rfl
lemma d_returns (b:ℕ)(ρ t:ℝ) : kite b ρ t W (D z k)= SitSpin.raw (seat W k) z (body W k).1 (body W k).2:=by funext n x; exact d_beats _ _ _ _ _ _
