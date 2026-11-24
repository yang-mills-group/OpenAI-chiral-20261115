import YM.SU5.Reconstruction.Based.Peeling
import YM.CF.Matter.Mass
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
/-! # U(1) markers by SITE with Spin sign. Not symmetries; for checking Profile only. -/
namespace Mixing
variable {K:Calibration}{N:Side}(x:Cover)(z:unitary ℂ)
noncomputable def emitter (N:Side)(v:Site N × SpinIdx): ℂ := if v.1=wrap N x then (if v.2∈plusHalf then z.val else star z.val) else 1
noncomputable def rayblock (v:Site N × SpinIdx):Op Slot:= emitter x z N v • 1
lemma bright (v:Site N× SpinIdx): emitter x z N v∈unitary ℂ:=by unfold emitter; split_ifs <;> first | exact z.property | exact Unitary.star_mem z.property | exact Submonoid.one_mem (unitary ℂ)
-- `tradew` uses this same index type.Need commute.
noncomputable def toneUnit(N:Side) : UNI (Single N) := ⟨jump (Equiv.refl _) (rayblock x z), jump_unitary _ _ (fun i=> Matrix.mem_unitaryGroup_iff.mpr (by rw [rayblock,star_smul,star_one,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,show emitter x z N i*star (emitter x z N i)=1 from (bright x z i).2,one_smul,one_mul]))⟩
lemma tone_comm (g:Seat N→ SU.E): Commute (toneUnit x z N) (tradew N g):=by
 apply Subtype.ext; unfold tradew toneUnit; change jump (Equiv.refl (Site N × SpinIdx)) (n:=SU.Slot) _*jump (Equiv.refl (Site N × SpinIdx)) (n:=SU.Slot) _=jump (Equiv.refl (Site N × SpinIdx)) (n:=SU.Slot) _ * jump (Equiv.refl (Site N × SpinIdx)) (n:=SU.Slot) _; rw [jump_mul,jump_mul]; congr 1; funext i
 change (_ • (1:Op _))*_ = _ * (_ • _); rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm, one_mul,mul_one]; rfl
lemma tone_kind (g:Seat N→ SU.E): Commute (quantU (toneUnit x z N)) (quantU (tradew N g)):= by
 apply Subtype.ext; let a:=toneUnit x z N; let b:=tradew N g; change quant a.val * quant b.val=quant b.val * quant a.val; rw [← quant_mul,← quant_mul,show a.val*b.val=b.val*a.val from congrArg Subtype.val (tone_comm x z g).eq]

lemma tone_basis (v:Site N×SpinIdx)(c:SU.Slot): acts (toneUnit x z N).val (basisKet (v,c))=emitter x z N v • basisKet (v,c):=by
 apply PiLp.ext; rintro ⟨a,b⟩; change (acts (jump (Equiv.refl (Site N × SpinIdx)) (rayblock x z)) _).ofLp _= _; simp only [basis_act,WithLp.ofLp_smul,Pi.smul_apply,basis_apply,jump_apply,Equiv.refl_apply, rayblock, Matrix.smul_apply,Matrix.one_apply]; by_cases g:a=v <;> by_cases h:b=c <;> simp [g,h]
-- all physically unwrapped on one moment
lemma still_tone (y:Cover)(i:SpinIdx)(a:SU.Slot)(p:Hosp S N)(t:nodeC x∈ S)(v:nodeC y∈ S):
    acts (toneUnit x z N).val (basisC N y i a)= (if x=y then (if i∈plusHalf then z.val else star z.val) else 1) • basisC N y i a:=by
 unfold basisC Lifted.index; rw [map_smul,tone_basis,smul_comm (winding N y)]; unfold emitter; by_cases h:x=y; · subst x; simp
 rw [if_neg h,if_neg]
 intro e; exact h (nodeC_inj (p.seat_ t v (by rw [←node_of,←node_of]; exact congrArg node (Eq.symm e))))
lemma beamsCreate (y:Cover)(i:SpinIdx)(a:SU.Slot)(p:Hosp S N)(t:nodeC x∈ S)(v:nodeC y∈ S)(h:i∈plusHalf): twist (quantU (toneUnit x z N)) (create (basisC N y i a))=(if x=y then z.val else 1:ℂ) • create (basisC N y i a):=by rw [twist_create, still_tone x z y i a p t v,if_pos h,map_smul]
lemma beamsRemove (y:Cover)(i:SpinIdx)(a:SU.Slot)(p:Hosp S N)(t:nodeC x∈ S)(v:nodeC y∈ S)(h:i∉plusHalf): twist (quantU (toneUnit x z N)) (Fock.remove (basisC N y i a))=(if x=y then z.val else 1:ℂ) • Fock.remove (basisC N y i a):=by rw [twist_remove, still_tone x z y i a p t v,if_neg h]; unfold Fock.remove; rw [map_smul,star_smul]; split<;> simp

variable {k:ℕ}(K:Calibration)(W:Window.Family)(p:Fin k→ Cover)
local notation "B"=> Stitches K W p S
local notation "Γ"=> raw S K W p
local notation "D" a:max=> scene S K W p l a (removal K) (creation K) (scalar K) -- l binder later
variable {Q:Family K}{μ:Multiset Cover}{l:List (Fin k)}{m:Side}
variable (v:Hosp S (K.c m))(h:nodeC x∈ S)
local notation "nu" => twist (quantU (toneUnit x z (K.c m)))
def Accounts (z:ℂ) (U:Fields (K.c m))(A:UNI (Finset (Single (K.c m)))): Submodule ℂ (Family K) where
 carrier:={f| twist A (f m U)= z • f m U}
 zero_mem':=by change twist A (0:FC (Single (K.c m)))= z • 0; rw [map_zero,smul_zero]
 add_mem':=fun {f g} a b=> by change twist A _= z • (f m U+g m U); rw [show (f+g) m U=f m U+g m U from rfl,map_add,show twist A _=_ from (show twist A (f m U)=_ from a),show twist A _=_ from (show twist A (g m U)=_ from b), smul_add]
 smul_mem':=fun i f a=>by change twist A (i • f m U)= z • (i • f m U); rw [twist_scalar, show twist A _ =_ from (show twist A (f m U)=_ from a),smul_comm]
include h v
lemma stitch_eval (u:B (removal K) (creation K) l μ Q)(U:Fields (K.c m)): twist (quantU (toneUnit x z (K.c m))) (Q m U)= (z.val^μ.count x) • Q m U:=by
 induction u with
 | empty=> simp
 | @put i y c d a b l μ f ea eb ha hb ay k R' _ ih=>
    let A:= Fock.remove (basisC (K.c m) (p i) c a); let D':= create (basisC (K.c m) y d b); let T:= f m U
    change nu (A*D'*T)= _ • (A*D'*T); rw [map_mul, map_mul,beamsRemove x z (p i) c a v h k ha,beamsCreate x z y d b v h ay hb,show nu T=_ from ih];
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,smul_smul, Multiset.count_cons,pow_add]; split_ifs <;> (simp only [pow_one,pow_zero]; apply (fun h=>congrArg (fun z:ℂ=> z • (A*D'*T)) h); ring)
lemma scene_accounts (μ:Multiset Cover)(l:List (Fin k))(U:Fields (K.c m)): scene S K W p l μ (removal K) (creation K) (scalar K) ≤ Accounts K (z.val^μ.count x) U (quantU (toneUnit x z _)):=by
 apply Submodule.span_le.mpr; rintro _ ⟨A,g,e,hg,rfl⟩
 change nu (scalar K g m U*A m U)= _ • (scalar K g m U*A m U); rw [map_mul, stitch_eval x z K W p v h e]; simp only [scalar,twist_scalar,map_one,Algebra.mul_smul_comm]
lemma raw_accounts (μ:Multiset Cover)(U:Fields (K.c m)): raw S K W p μ ≤ Accounts K (z.val^μ.count x) U (quantU (toneUnit x z _)):= by
 apply Submodule.span_le.mpr; rintro f ⟨l,q,b,e⟩; exact scene_accounts x z K W p v h μ l U e
lemma raw_eval (t:Q∈raw S K W p μ)(U:Fields (K.c m)): twist (quantU (toneUnit x z (K.c m))) (Q m U)=(z.val^μ.count x) • Q m U:= raw_accounts x z K W p v h μ U t
omit h v
-- primitive roots for arbitrarily discriminating
lemma discriminant (a b:ℕ) (h:a≠b):∃ r:unitary ℂ, r.val^a≠r.val^b:=by
 let n:=a+b+1; have k:n≠0:=by dsimp only [n]; omega
 let z:= Complex.exp (2*Real.pi*Complex.I/(n:ℂ)); have ht: IsPrimitiveRoot z n:=Complex.isPrimitiveRoot_exp n k -- may need pos version
 have hb: ‖z‖=1:= (pow_left_inj₀ (norm_nonneg z) zero_le_one k).mp (by rw [← norm_pow,ht.pow_eq_one]; simp)
 have hz:z*star z=1:=by rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hb]; norm_num
 refine ⟨⟨z,mul_comm z _ ▸ ?_,hz⟩,?_⟩ -- syntax error unitary
 all_goals first | exact hz | exact fun e=> h (ht.pow_inj (by dsimp only [n]; omega) (by dsimp only [n]; omega) e)
end Mixing
end YM.CF.Buffered.Afterglow.Rooted
