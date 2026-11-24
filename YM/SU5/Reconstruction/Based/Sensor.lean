import YM.SU5.Reconstruction.Based.Decompose
import YM.SU5.FiniteGaugeData.Signal.Trumpet
set_option autoImplicit false
set_option synthInstance.maxSize 32000
set_option maxRecDepth 5000
set_option maxHeartbeats 900000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Rooted
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Fock Lat Cube SU Spire Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Next.Free Bloch Drapes Lifted Skye Girt Nacre Sound Tapestry Satin MeasureTheory Rush
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open WalkRoots Push.SectorMeasure
set_option quotPrecheck false
variable {S:Finset Cover}(R:RouteMap S)
-- genuine centre-phase at any removal site in that same nonzero footprint. Need keep reading
-- the actual coupled link, not contact not even substitute motion of auxiliary.
open Mixing
variable {m:Side}
-- adapt Signal.Ovation.Transit's gauge on this Cover. Even after physical transport; used
-- before changing Profile.Later levels keep whole test cost not this individual-center fact.
namespace Centre
open YM.CF.Signal.Ovation.Transit -- check prefix
variable (W:SU.Slot){i:SpinIdx}(x:Cover)(k:SU.Slot)
noncomputable def centerT(m: Side) : Seat m→ SU.E := lamp (wrap m x)
lemma kernelBasis (y:Cover) (p:nodeC x∈ S)(h:nodeC y∈ S)(e:Hosp S m)(q:Window.family k=Window.family W): acts (tradew m (centerT x m)).val (basisC m y i k)=(if x=y then zeta W else 1) • basisC m y i k:=by
 unfold centerT basisC; rw [map_smul,zfactor];
 change (winding m y:ℂ) • ((if wrap m y=wrap m x then zeta k else 1) • basisKet (Lifted.index m y i k))= _; rw [smul_comm]; have h0:zeta k=zeta W:=by obtain ⟨a,k|k⟩:=k <;> obtain ⟨v,W|W⟩:=W <;> simp [family] at q <;> rfl
 by_cases g:x=y; · rw [g]; simp [h0];
 rw [if_neg g,if_neg] -- maybe goal? tune
 intro u; exact g (nodeC_inj (e.seat_ p h (by rw [←node_of,←node_of]; exact congrArg node u.symm)))
end Centre
variable {k:ℕ}(K:Calibration)(b:SU.Slot)(p:Fin k→ Cover)(i:Fin k)
open YM.CF.Signal.Ovation.Transit Centre
local notation "B" => Stitches K (Window.family b) p S
local notation "Γ" => raw S K (Window.family b) p
local notation "η" => centerT (p i) (K.c m)
local notation "ρ" => removal K
local notation "π" => creation K
variable {Q:Family K}{μ:Multiset Cover}{l:List (Fin k)}
variable (v:Hosp S (K.c m))(h:nodeC (p i)∈ S)
local notation "V" => quantU (tradew (K.c m) (centerT (p i) (K.c m)))
include h v
lemma stitch_center (p₀:B (removal K) (creation K) l μ Q)(g:Fields (K.c m)): twist (V) (Q m g)= ((star (zeta b))^μ.count (p i)) • Q m g:=by
 induction p₀ with
 | empty=> simp
 | @put i' y c d a b' l μ f ea eb k v0 x z u e ih=>
    let A:= basisC (K.c m) (p i') c a; let D:= basisC (K.c m) y d b'; let X:= Fock.remove A; let Y:=create D; let P:=f m g
    let Tr (t:Cover):= if p i=t then zeta b else 1
    change twist V (X*Y*P)= _ • (X*Y*P)
    rw [map_mul,map_mul,show twist V P=_ from ih];
    rw [show twist V X=star (Tr (p i')) • X from (by unfold X Fock.remove; rw [map_star,twist_create,show acts _ A=_ from (show acts _ A=Tr (p i') • A from kernelBasis b (p i) a (p i') h z v ea),map_smul,star_smul]),show twist V Y=Y from (by unfold Y; rw [twist_create,show acts _ D=_ from kernelBasis b (p i) b' y h x v eb,if_neg (Ne.symm (u _)),one_smul])]
    simp_rw [Multiset.count_cons]; rw [if_neg (Ne.symm (u _)),Nat.add_zero]; unfold Tr; split_ifs <;> (simp only [star_one,pow_add,pow_one,pow_zero,mul_one,one_smul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; try rw [mul_comm (star (zeta b))] <;> try rfl)
    all_goals first | dsimp only [P] | rfl
lemma sensing (t:Injective p)(u:p i∈ μ)(V_:Fields (K.c m)): raw S K (Window.family b) p μ ≤ Accounts K (star (zeta b)) V_ V:=by
 apply Submodule.span_le.mpr; rintro f ⟨l,a,q,e⟩
 suffices u: scene S K (Window.family b) p l μ (removal K) (creation K) (scalar K) ≤ Accounts K (star (zeta b)) V_ V from u e
 apply Submodule.span_le.mpr; rintro f ⟨g,h',A,B',rfl⟩
 have T:μ.count (p i)=1:=Nat.le_antisymm ((A.count_of_anchor i t) ▸ (List.nodup_iff_count_le_one.mp q) i) (Nat.succ_le_of_lt (Multiset.count_pos.mpr u))
 change twist V (scalar K h' m V_*g m V_) = _ • (scalar K h' m V_ * g m V_); rw [map_mul,stitch_center K b p i v h A V_,T,pow_one]; simp only [scalar,twist_scalar,map_one,Algebra.mul_smul_comm]
lemma coupled {Q:Family K}(e:Neutral K Q)(q:Q∈connected R K (Window.family b) p μ)(t:Injective p)(z:p i∈ μ)(U U':Pane (K.c m)):
    Q m (gauge (centerT (p i) (K.c m)) U,U')=star (zeta b) • Q m (U,U') ∧
    (Q m (U,U')≠0 → Q m (gauge (centerT (p i) (K.c m)) U,U')≠ Q m (U,U')):=by
 have ht:Q m (gauge (centerT (p i) (K.c m)) U,U')=star (zeta b) • Q m (U,U') := by
    obtain ⟨g,h',hg⟩:=(paid_on_charge R K (Window.family b) p q).visits.only_cont m
    rw [show Q m _= Q m (simultaneous η (U,U')) from (by rw [h']; rfl), e m]
    exact sensing K b p i v h t z _ (restore_component R K (Window.family b) p μ q)
 refine ⟨ht,fun u g=>?_⟩; rw [ht] at g; apply charge_one b; exact (smul_left_injective ℂ u) (g.trans (one_smul ..).symm)
end YM.CF.Buffered.Afterglow.Rooted
#print axioms YM.CF.Buffered.Afterglow.Rooted.coupled
