import YM.CF.BProof.Fine.Reduction
import YM.CF.BProof.Mote.Plan
import YM.CF.BProof.Solar.Right
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive Tap Haro
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye
set_option synthInstance.maxSize 28000
namespace Leg
variable {m n : Type}[LinearOrder m][Fintype m][LinearOrder n][Fintype n]
variable {N P:Side}(G:Ratio N P)(j:ℕ) (Q:SpaceM)(M:Male)
open TripD
open Reed (Fine)
open Temper RG
lemma finale (S:Support (More N))(A:FC (Single N))(h:Sector (modes S) false A):∃ F,Snow S false F∧Temper.rel (mateK _) A F:=by
 obtain ⟨F,p,t⟩:= Temper.comf.final (S:=Tset N) h
 let U:= mateK N; refine ⟨F,p,?_⟩; have ht: acts (cutM {Tset N}) U=U:=by rw [←cutLine,←touchP]; exact (tickB N).1 -- tune direction
 unfold Temper.rel; have hu:U=U.ofLp (Tset N) • basisKet (Tset N):= ht.symm.trans (cut_oneAct ..); change acts _ U=acts _ U; rw [hu,map_smul,map_smul,show acts _ _=_ from t]
attribute [local instance] Bide.mCast Bide.bCast
variable (i:Axis){S:Support (More N)}{F:Obs N}
lemma mellow (p:Allowed S F) :∃ X:Obs N, Allowed S X∧(∀ U, Snow S false (X U))∧∀ U, Temper.rel (mateK N) (F U) (X U):=by
 let W:= profileB (modes S) false; let K:= Module.finBasis ℂ W; choose f hY u using fun i=> finale S (K i).val (K i).property
 let T (y:Pane N):W:=⟨F y, p.modes_use _⟩; let G(y:W):FC (Single N):=∑ i,K.repr y i • f i; let V:=G ∘ T
 have he:Continuous G:= continuous_finsetSum _ fun i _=> (K.coord i).continuous_of_finiteDimensional.smul continuous_const
 have hc:Measurable T:=p.bounded.meas.subtype_mk; obtain ⟨w,h⟩:=p.bounded.cost; have hw: Envelope T:=⟨hc,w,h⟩; have hf(y):Snow S false (G y):=Fine.sumF _ _ (fun i _=> Fine.scale (hY i) _)
 refine ⟨V,⟨Girt.pole_w T G he hw,fun i j h=> congrArg G (Subtype.ext (p.reads i j h)),fun U=>(hf (T U)).sector⟩,fun U=>hf (T U),?_⟩
 intro U; let z:=T U; let x(i): FC (Single N):= K.repr z i • (K i).val; let y(i):FC (Single N):= K.repr z i • f i
 have ht: F U= ∑ i, x i:=by
    change W.subtype z=∑ i,x i; unfold x; change _=∑ i,K.repr z i • W.subtype (K i); simp_rw [←map_smul,←map_sum W.subtype,K.sum_repr]
 change Temper.rel _ _ (∑ i,y i); rw [ht]; generalize (Finset.univ : Finset (Fin (Module.finrank ℂ (↥W))))=s; induction s using Finset.induction_on with| empty=> simp only [sum_empty]; exact rfl| insert i s v t=> rw [sum_insert v,sum_insert v]; exact Temper.rel.plus ((u i).smul _) t
lemma reflet {A B:FC (Single N)}(p:Temper.rel (mateK _) A B): Temper.rel (mateK N) (theta (Fixed.reflectP N i) A) (theta (Fixed.reflectP N i) B):=by
 let U:= Fixed.mirrorWave (N:=N) i; let S:=Fixed.reflectP N i; have ht(x:FC (Single N)): U (acts x (mateK N))=acts (theta S x) (mateK N):=by unfold U; rw [Fixed.mirror_apply,Fixed.twist_mate, Reed.reverseW]; change acts ((1:ℂ) • _) _=_; rw [one_smul]; -- equality S def
 unfold Temper.rel; rw [←theta_star,←theta_star,← ht,← ht]; exact congrArg U p
lemma distill (p:Allowed S F) (g:Disjoint S (regionD (Fixed.reflectSweep N i) S)) :∃ X, Allowed S X∧ (∀ U,Snow S false (X U))∧∀ Y:Orbit N→Phys N,Fixed.functional Y (Chalk.un i F)=Fixed.functional Y (Chalk.un i X):=by
 obtain ⟨X,v,h,t⟩:= mellow p; let U:=Fixed.reflectSweep N i; let m' := Chalk.mirror (N:=N) i
 have hO{F:Obs N}(p:Allowed S F):Allowed (regionD U S) (Chalk.mirror i F):=by rw [Chalk.mirror,← BProof.Bide.origin i (plain p)]; exact movement p (by rfl)
 have hp(A:Pane N) : Temper.rel (mateK N) (m' F A) (m' X A):=by unfold m'; rw [Chalk.mirror₀,Chalk.mirror₀]; exact reflet i (t _)
 have hx: m' X * F= F *m' X:= (Allowed.commute p (hO v) g).symm.eq; have hv: m' X*X=X*m' X:= ((v.commute (hO v) g).symm.eq)
 refine ⟨X,v,h,fun Y=> integral_congr_ae (Eventually.of_forall fun y=> ?_)⟩
 let z:= y.1; have he: Temper.rel (mateK _) (m' F z*F z) (m' X z * X z):=by
    refine (Temper.rel.mul_right (hp z) (F z)).trans ?_; change Temper.rel _ ((_ * _ :Obs N) z) ((_ * _:Obs N) z); rw [hx,hv]; exact (t z).mul_right (m' X z)
 exact he.bra _
end Leg
end YM.CF.BProof.Bide
