import YM.SU5.Exchange.Stack.Louvre
import YM.CF.Stax.Bust
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Tulip Lat Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive  Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU
variable (s:Sweep n)
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single n
local notation "Fz"=> FC (Dwell n)


abbrev roll (s:Sweep n):= lotY s.charge (detX s.s) (γS s)
lemma sweet (e r:Bool) (U:UNI (Single n))(x:Fz): lotY e r U (star x) = star (lotY e r U x) :=by
  change sauce e r U (star x)=star (sauce e r U x);unfold sauce; rw [singT, singT, win_s, map_star]
lemma calque (x:Bool)(i j: Single n):
    ‖(crib T D₁ x).val j i‖= ‖(T).val j i‖:=by
    -- adjust
    generalize T=u
    generalize D₁=d
    cases d <;> cases x <;> simp [crib,Pastry.thread,ccU,filmG]


-- NOTE Gauge coherence needed on literal even Fock matrices, prove direct
-- via Fock.Sector induction on puts.
lemma blanket {W:Support (More n)} {v:Bool}{A:Fz}
   (z:Sector (camp W) v A): Sector (camp (actY s W)) v (roll s A):=by
   have per (j:Dwell n) (p:j∈camp W):
       Sector (camp (actY s W)) true (roll s (put j)) ∧
       Sector (camp (actY s W)) true (roll s (takeF j)):=by
     rcases j with ⟨x,j⟩

     unfold roll
     have lady {i:Single n} (hi:(crib T D₁ x).val i j≠0):
         ((x.xor D₁,i):Dwell n)∈camp (actY s W):=by
       refine mem_filter.mpr ⟨mem_univ _, mem_map_equiv.mpr ?_⟩
       change boxA s (node i.1.1)∈W
       rw [show boxA s (node i.1.1)=node j.1.1 from
          Tye.birth_l i j (castX s) _ _ (norm_ne_zero_iff.mp ((calque s x j i).symm ▸ norm_ne_zero_iff.mpr hi))] -- eq orientation
       exact (mem_filter.mp p).2
     -- take=star
     rw [show takeF (x,j) = star (put (x,j)) from ?_,sweet, L_mile]
     · constructor
       · apply Sector.sumS; intro i _
         by_cases h:(crib T D₁ x).val i j=0
         · rw [h,zero_smul];exact Sector.zero _
         exact (Sector.up _ (lady h)).scale _
       unfold f_sound; rw [star_sum]
       apply Sector.sumS;intro i _
       by_cases h:(crib T D₁ x).val i j=0
       · rw [h,zero_smul,star_zero];exact Sector.zero _
       rw [star_smul]
       change Sector _ _ (starRingEnd ℂ _ • takeF _)
       exact (Sector.down _ (lady h)).scale _
     rfl
   induction z with
   |one => rw [map_one];exact Sector.one
   |zero => rw [map_zero]; exact Sector.zero _
   |up i p=> exact (per i p).1
   |down i p=> exact (per i p).2
   |scale z x y=> rw [roll,Ione.G_lot];exact y.scale _
   |add x y z w=> rw [map_add];exact z.add w

   |mul x y z w=> rw [map_mul];exact z.mul w

lemma saxy (x:Bool) (i:Single n): ∑ j:Single n, ‖(crib T D₁ x).val j i‖ ≤ Tenant.quota:=by
  simp_rw [calque s x]
  exact ρ_K ..
section
variable {n':Type}[LinearOrder n'][Fintype n']
lemma tumulus {A:FC n'} (e:Ark A h a)(p:a ≤ b)(u:0≤h):
   Ark A h b :=
   ⟨e.positive.trans p,fun j=>(e.tubes j).trans (mul_le_mul_of_nonneg_right p (pow_nonneg u _))⟩
lemma rubble {α:Type}[Fintype α](u:α→ℂ)(A:α→FC n')(p:∀i,Ark (A i) h h)
   (v:0≤h): Ark (∑i:α,u i • A i) h ((∑i:α,‖u i‖)*h):=by
    refine ⟨by positivity,fun j=>?_⟩
    have hc(i:Finset n') : ‖(∑ y:α,u y • A y) i j‖ ≤ ∑y:α,‖u y‖*‖A y i j‖:=by
       rw [Matrix.sum_apply]
       exact (norm_sum_le ..).trans (le_of_eq (by simp))
    refine le_trans (sum_le_sum (s:=univ) (fun i _=>mul_le_mul_of_nonneg_left
       (hc i) (pow_nonneg v _))) ?_
    simp_rw [mul_sum]
    rw [sum_comm,mul_assoc,sum_mul]
    exact sum_le_sum fun i _=>by
       simp_rw [mul_left_comm (h^_) ‖u i‖, ←mul_sum]; exact mul_le_mul_of_nonneg_left ((p i).tubes j) (norm_nonneg _)
end

lemma hoop (u:1≤h) (x:Dwell n):Ark (roll s (put x)) h (Tenant.quota*h) ∧ Ark (roll s (takeF x)) h (Tenant.quota*h):=by
  have y:=zero_le_one.trans u
  cases x with | mk x j=>
    unfold roll
    let Tj(i:JS):=(x.xor D₁,i)
    let vx(i:JS):=(crib T D₁ x).val i j
    rw [show takeF (x,j)=star (put (x,j)) from rfl, sweet,L_mile,f_sound,star_sum]
    constructor
    · exact tumulus (rubble vx (put ∘ Tj) (fun i=>Ark.blond h u _) y)
         (mul_le_mul_of_nonneg_right (saxy s x j) y) y
    simp_rw [star_smul]
    refine tumulus (rubble (star ∘ vx) (takeF ∘ Tj) (fun i=>Ark.bud h u _) y) (mul_le_mul_of_nonneg_right ?_ y) y
    simpa [vx] using saxy s x j

open Hive
lemma yum {Z:Finset (Dwell n)}{v:Bool}{X:Fz}
   (g:Site (More n)→E) (p:Sector Z v X):
   roll s (lotY false false (tradew n g) X) = lotY false false (tradew n ((polarT s.charge ∘g) ∘ (castX s).anon n)) (roll s X):=by
 let y:=(tradew n g); let w:=(tradew n ((polarT s.charge ∘g) ∘ (castX s).anon n))
 have l(j:Dwell n): roll s (lotY false false y (put j))=lotY false false w (roll s (put j)):=by
   cases j; unfold roll w y
   change lotY _ _ (siteU _ _ _ n) _=lotY _ _ _ (lotY _ _ (siteU _ _ _ n) _)
   rw [Ione.honey,Ione.honey,tr_s]
   have hi(e:Bool): feeJ false e=1:=by cases e <;> rfl
   have hu(e:Bool): feeJ e false=1:=by cases e <;> rfl
   simp only [hi,Bool.false_xor,hu,one_smul,site_ui,Bool.xor_false,whiten,Bool.false_eq_true,↓reduceIte,envoy]
 induction p with
 |one=> simp only [map_one]
 |zero=> simp only [map_zero]
 |up j e=>exact l j
 |down j e=> unfold roll; rw [show takeF j=star (put j) from rfl,sweet,sweet,sweet,sweet]; exact congrArg star (l j)
 |scale p z t => unfold roll;rw [G_lot,G_lot,G_lot,G_lot]; congr 1 -- tune
 |add x y z t=>rw [map_add,map_add,map_add,map_add,z,t]
 |mul x y z t=>rw [map_mul,map_mul,map_mul,map_mul,z,t]

-- Ark supporting specific modes, sold at extra quota².
abbrev Spinner (h:ℝ)(Z:Single n→Single n→FC (Dwell n)):Prop:=
  ∀ (s:Sweep n)(i j:JS), Ark (roll s (Z i j)) h (Tenant.quota^2*h^2)
variable (h)(u:1≤h)
include u
open Sault
lemma oreSpin : Spinner h (coreK (n:=n)) := by
   intro s i j
   unfold coreK
   have w:1≤Tenant.quota^2:=one_le_pow₀ ((by norm_num: (1:ℝ)≤16).trans Tenant.quota_bound)
   split
   · rw [map_one]; exact tumulus (Ark.one h) (one_le_mul_of_one_le_of_one_le w (one_le_pow₀ u)) (zero_le_one.trans u)
   rw [map_zero]; refine ⟨by positivity,fun j=>?_⟩
   have h:=zero_le_one.trans u; simp; positivity
lemma palSpin : Spinner h (n:=n) (fun i j=>wire true i*wire false j):=by
  intro s i j; rw [map_mul,←mul_pow,sq]
  exact Ark.opus h u (hoop s u ((true,i):Dwell n)).1 (hoop s u ((false,j):Dwell n)).1
lemma lessSpin : Spinner h (n:=n) (fun i j=>trailM false i*trailM true j):=by
  intro s i j; rw [map_mul,←mul_pow,sq]
  exact Ark.opus h u (hoop s u ((false,i):Dwell n)).2 (hoop s u ((true,j):Dwell n)).2
lemma legSpin : Spinner h (n:=n) (fun i j=>wire true i * trailM true j):=by
  intro s i j; rw [map_mul,←mul_pow,sq]
  exact Ark.opus h u (hoop s u ((true,i):Dwell n)).1 (hoop s u ((true,j):Dwell n)).2

lemma tailSpin : Spinner h (n:=n) (fun i j=> -(wire false j*trailM false i)):=by
  intro s i j; rw [map_neg,map_mul,←mul_pow,sq]
  have v:=Ark.opus h u (hoop s u ((false,j):Dwell n)).1 (hoop s u ((false,i):Dwell n)).2
  exact ⟨v.positive,fun x=>by simp_rw [Matrix.neg_apply,norm_neg]; exact v.tubes _⟩
end YM.CF.Organdy
