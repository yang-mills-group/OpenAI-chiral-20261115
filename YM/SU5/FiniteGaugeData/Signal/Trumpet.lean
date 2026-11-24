import YM.SU5.FiniteGaugeData.Signal.Attestation
/-! # Limiting state compatibility of activated nonzero signal. This one state at all floors/moments.
 Physical `Y.Λ` pivot predates all floors or tv shrink. Accountant error μ on μ period & sharp path,
 witness transported actual at fixed separation **NOT renormalized to UV margin through inverse graft**.
 Lease dimensions always confirmed through assignment; only claim sterile read regarding means of special
 unbalanced chiral class. Continuum, vacuum and OS strict correlation not asserted by this result.
 -/
set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 760000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper IgnoreFog Vale Period
open Buffered.Reliance Buffered.Reliance.ShortWave Afterglow Afterglow.Journey
open Boon Graph Pressure Esti Jade.Earn Phase CF.Laic CF.Ember
open Escalator Concord Boon Parfume
namespace Ovation
namespace Transit
variable {N n:Side} (i:Site N)(m k:SU.Slot)
local notation "G"=> SU.E
def lamp (l:Site N):Plum.Troupe N:=fun t=> if t=node l then SU.central else 1
local notation "U" i:max => tradew N (lamp i)
local notation "Q" i:max => quantU (tradew N (lamp i))
def zeta (l: SU.Slot):ℂ:= SU.z^SU.charge l
lemma charge_one : star (zeta k) ≠ 1 := by intro hz; have h:zeta k=1:= star_injective (show star (zeta k)=star 1 from hz.trans (star_one _).symm); have hp:= z_prim.dvd_of_pow_eq_one _ h; obtain ⟨a,b|b⟩:= k <;> simp [SU.charge] at hp
private lemma charge_family (e:Window.family k= Window.family m): zeta k=zeta m:= by obtain ⟨x,k|k⟩:=k <;> obtain ⟨y,m|m⟩:=m <;> simp [Window.family] at e <;> rfl
private def pearlK {N:Side}(i:Site N)(x:Single N):ℂ:= if x.1.1=i then zeta x.2 else 1
lemma zfactor (v:Single N): acts (tradew N (lamp i)).val (basisKet v) = pearlK i v •basisKet v:=by
 apply PiLp.ext; rintro ⟨b,j⟩; obtain ⟨a,k⟩:=v; simp only [basis_act,WithLp.ofLp_smul,Pi.smul_apply,basis_apply]
 by_cases h:b=a; · subst b; by_cases u:a.1=i <;> by_cases t:j=k<;> simp [tradew,jump_apply,- SU.matter_matrix,u,t,pearlK,lamp,zeta,show node a.1=node i↔a.1=i from needle.eq_iff, by_charge, show (1: UNI SU.Slot).val=(1:Op _) from rfl, Matrix.one_apply]
 simp [tradew, jump_apply,h]
local notation "Λ" i:max => FC (Single i)
def Key (V:UNI (Finset (Single N)))(a:ℂ): Submodule ℂ (FC (Single N)) where -- twist accepts FC quant label? seal Single = finset?
 carrier:={x|twist V x = a • x}
 zero_mem':= by change twist V (0:FC _)=_; simp
 add_mem':=fun {x y} e p=> by change twist V _ = _; rw [map_add,show twist V _ =_ from e, show twist V _= _ from p,smul_add]
 smul_mem':=fun c x p=>by change twist V _ = _; rw [twist_scalar,show twist V _ = _ from p,smul_comm]
-- tuned
lemma key_mul (V:UNI (Finset (Single N))) (a b:ℂ): Key V a*Key V b ≤ Key V (a*b):= Submodule.mul_le.mpr fun x p y t=> by change twist V _ = _; rw [map_mul,show twist V x=_ from p, show twist V y=_ from t,mul_smul, Algebra.smul_mul_assoc,Algebra.mul_smul_comm]

local notation "𝒯"=> Key (quantU (tradew N (lamp i)))
lemma keyArrival (S:Finset (Site N))(t:i∉S): arrivals (family k) S ≤ 𝒯 1:= by
 refine Submodule.span_le.mpr ?_; rintro _ ⟨v,e,rfl⟩; change twist _ _ = _; rw [←create_put,twist_create,zfactor,map_smul,pearlK,if_neg (fun (d:v.1.1=i)=> t (d ▸ (mem_filter.mp e).2.1))]
lemma keyDepart (j:Site N): removals (family k) j ≤ 𝒯 (if j=i then star (zeta k) else 1) := by
 refine Submodule.span_le.mpr ?_; rintro _ ⟨v,e,rfl⟩; change twist _ _ = _; rw [←remove_take,twist_remove,zfactor]; unfold Fock.remove; rw [map_smul,star_smul]; rw [pearlK,mem_singleton.mp (mem_filter.mp e).2.1,charge_family _ _ (mem_filter.mp e).2.2.2]; split<;> simp
lemma key_books (S:Finset (Site N))(t:i∉S)(j:Site N) : books (family k) S j ≤ 𝒯 (if j=i then star (zeta k) else 1):=(mul_le_mul' (keyDepart i k j) (keyArrival i k S t)).trans ((key_mul (Q i) _ 1).trans_eq (by rw [mul_one]))
-- ony if aperture missing use χ=1
lemma keyGrace (S:Finset (Site N))(t:i∉S)(L: List (Site N))(h:L.Nodup): generous (family k) S L ≤ 𝒯 (if i∈L then star (zeta k) else 1):=by
 induction L with
 | nil=> rw [if_neg (List.not_mem_nil)]; exact Submodule.one_le.mpr (by simp [Key]) -- conv
 | cons j L ih=>
    let x(l:List (Site N)):ℂ:= if i∈ l then star (zeta k) else 1; let a:= x L
    simp only [generous,List.map_cons,List.prod_cons]; apply le_trans (mul_le_mul' (key_books i k S t j) (ih (List.nodup_cons.mp h).2)); apply le_trans (key_mul ..)
    by_cases t:j=i; subst j; simp [(List.nodup_cons.mp h).1]; simp [t,Ne.symm t]
end Transit
end Ovation
end YM.CF.Signal
#print axioms YM.CF.Signal.Ovation.Transit.keyGrace
