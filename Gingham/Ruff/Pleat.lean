import Gingham.Ruff.Farina
import YM.CF.Fief.Lucid
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Hake Tenant
set_option linter.unusedSimpArgs false


-- join a (route) tail to y.
lemma quilt (x y:Site N) (S:Support N) (v:Grove (terr N) S)
    (h:x∈S): ∃ D:Support N, S⊆D ∧ y∈D ∧ Grove (terr N) D ∧ D.card ≤ S.card+4*separation x y := by
  have stitch (w:Lattice.Walk)(z:Site N)(S:Support N)(u:z∈S)(p:Grove (terr N) S):
    ∃ D:Support N,S⊆D ∧ stop z w ∈D ∧ Grove (terr N) D ∧ D.card ≤ S.card+w.length:=by
    induction w generalizing z S with
    | nil => exact ⟨_,le_rfl,u,p,(Nat.add_zero _).ge⟩
    | cons d w ih =>
      let k : Site N := z+d.vec -- remove
      have t:(terr N).span k z ≤ 1 := by
        change separation (z+d.vec) z≤_
        rw [separation,add_sub_cancel_left, Step.vec]
        split
        · rw [pdist_neg];exact pdist_step _
        exact pdist_step _
      obtain ⟨D,a,b,c,f⟩:=ih k _ (mem_insert_self k _) (Grove.join p u t)
      exact ⟨D,(subset_insert _ _).trans a,b,c,
        f.trans ((Nat.add_le_add_right (card_insert_le ..) _).trans (by simp;omega))⟩
  have s (z q:Site N) (w:Lattice.Walk): stop (z+q) w=stop z w + q :=by
    induction w generalizing z with
    | nil => rfl
    | cons p w ih => rw [stop,stop,add_right_comm,ih]
  obtain ⟨D,a,b,c,f⟩:=stitch (turncoat (y-x)) x S h v
  have bx:=s 0 x (turncoat (y-x))
  rw [zero_add,turncoat_distance,sub_add_cancel] at bx
  refine ⟨_,a,bx▸b,c,f.trans ?_⟩
  rw [separation_comm,separation]
  gcongr;exact turncoat_size _

open scoped Classical
lemma coverMono(k:ℕ) {X Y:Support N}(u:X⊆Y): coverNumber k X ≤ coverNumber k Y:=by
  obtain ⟨d,p,q⟩:=coverNumber_realized k Y
  exact Nat.find_min' (covers_some k X) ⟨d,⟨u.trans p.1,p.2⟩,q⟩

variable {a E:ℝ} {l r b w:ℕ}
def footprint (o : Site N)(S : Support N)(l r b:ℕ):=
  Lattice.halo (l*b) {o} ∪ Lattice.halo (r+10) S
def pique (b:ℕ)(E:ℝ)(X:Support N):=Real.exp (E*(coverNumber b X:ℝ))
def Tallow (a E:ℝ)(w l:ℕ):=Real.exp (E*(Fief.tileN l:ℝ)+a*w)
-- a is rate to spend (e.g. a/8), exponent savings buys footprint over typical root geometry.
lemma threadbare {o: Site N}(S:Support N)(x:Site N)(i:x∈S)
    (v:Grove (terr N) S)(t:separation o x ≤ w+5*S.card)
    (h:0<b)(z:r+10≤l*b)(k:0<a)(p:0≤E)
    (H:42*E*Fief.tileN l≤a*b):
    pique b E (footprint o S l r b) ≤ Tallow a E w l * Branch.rent a S:=by
  obtain ⟨D,u,oM,hD,bD⟩:= quilt x o S v i
  have sub: footprint o S l r b ⊆ Lattice.halo (l*b) D:=union_subset
    (Corona.halo_mono le_rfl (singleton_subset_iff.mpr oM)) (Corona.halo_mono z u)

  have one(y:Site N):(idrat N).parent y=y:=by
    nth_rw 1 [←glass y]
    exact Ratio.embed_parent ..
  have u:=Fief.fen (idrat N) D b l h (a*2/21) E (by positivity) p (by
    rw [show (idrat N).count.val=1 from rfl,Nat.cast_one]; linarith only [H]) hD
  rw [show D.image (idrat N).parent=D by ext;simp [one]] at u
  refine le_trans ((show pique b E (footprint o S l r b)≤pique b E (Lattice.halo (l*b) D)
    from Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (coverMono b sub)) p)).trans u) ?_
  have d:(D.card:ℝ)≤(4*w+21*S.card:ℝ):=by
    norm_cast
    rw [separation_comm] at t; omega
  unfold Branch.rent Tallow; rw [←Real.exp_add,←Real.exp_add];apply Real.exp_monotone
  nlinarith only [mul_le_mul_of_nonneg_left d k.le, mul_nonneg k.le (Nat.cast_nonneg w)]

variable {e:ℝ}{R:Seal (Seat N)→Prop}
   {A:Fob N e} -- e
def watt (y:Site N)(E:ℝ)(l r b:ℕ)(q:ℝ) (cost:Seal (Seat N) → Toll (Single N)):ℝ:=
 ∑ i:Single N,∑ j:Single N,∑ S,pique b E (footprint (bouton y) S l r b)*Branch.rent q S*cost S i j


variable {y:Site N}{u:Side}{q c:ℝ}
lemma lit {d:ℝ}(H:Buttons N e R a c A)(G:∀ S,R S → Girder y u S)
    (h:0<b)(z:r+10≤l*b)(k:0<d)(p:0≤E)
    (B:42*E*Fief.tileN l≤d*b)(v:d+q≤a):
    watt y E l r b q H.cost ≤ Tallow d E (widthL u) l * c:=by
  apply le_trans _ (mul_le_mul_of_nonneg_left H.paid (Real.exp_pos _).le)
  simp only [watt,savings,saleM,mul_sum]
  refine Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j _=>Finset.sum_le_sum fun S _=>?_
  by_cases t:H.cost S i j=0
  · simp [t]
  obtain ⟨g,iM,_⟩:=((H.pass S).expo i j).triggered t
  have F:=threadbare S _ iM g (G S (H.good S i j t) _ iM) h z k p B
  rw [←mul_assoc _ (Branch.rent a _)]
  apply mul_le_mul_of_nonneg_right _ ((H.pass S).nonn i j)
  apply le_trans (mul_le_mul_of_nonneg_right F (rent_pos ..).le)
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  unfold Branch.rent;rw [←Real.exp_add,← add_mul]
  exact Real.exp_monotone (mul_le_mul_of_nonneg_right v (Nat.cast_nonneg _))

def tenderb(b:ℕ):= b/200

variable (y:Site N)
abbrev ButtonsCut (y:Site N)(u:Side)(m:ℕ)(e:ℝ):=
 Buttons N e (fun S=> Girder y u S ∧ S.card ≤ m)


/-- Credentials, a = initial Plume rate. Given c (buttons) and selling at price E
  include both l*b root core and fixed Loom halo. u = half gauge units in price tick.
  b radiusB, r Loom width. -/
structure Tagbill(a E:ℝ)(u:Side)(l r b:ℕ) : Prop where
 apos : 0<a
 Epay : 0≤E
 largeL: 2≤l
 largeB: 500*(r+widthL u+10)≤b
 pays : 42*E*Fief.tileN l ≤ (a/16)*b

variable {y}
lemma Tagbill.size(Γ:Tagbill a E u l r b):
  0<b ∧ r+10≤l*b:=by
 have t:=Γ.largeL; have p:=Γ.largeB; have := Nat.mul_le_mul_right b t
 omega
variable (H:Plastron y u e (a/4) c A) (Γ:Tagbill a E u l r b)
def tagLite:ButtonsCut y u (tenderb b) e (a/4) (1*c) (H.light (tenderb b)):=H.lightP (tenderb b)
def tagFar:
 Buttons N e (fun S=>Girder y u S ∧ tenderb b<S.card) (a/8)
   (Real.exp (-(a/4-a/8)*(tenderb b:ℝ))*c) (H.flight (tenderb b)):=
   H.flightP (tenderb b) (by linarith [Γ.apos]) -- Γ not in statement, Lean auto include def
def fanbill (a E c:ℝ)(u:Side)(l:ℕ):=Tallow (a/16) E (widthL u) l*c

include Γ
lemma fanfareLite :
 watt y E l r b (a/16) (tagLite (b:=b) H).cost≤ fanbill a E c u l :=by


 simpa only [fanbill,one_mul c] using lit (q:=a/16) (y:=y)
   (tagLite (b:=b) H) (u:=u) (r:=r) (fun _ h=>h.1)
   Γ.size.1 Γ.size.2 (show 0<a/16 by linarith [Γ.apos]) Γ.Epay Γ.pays (by linarith [Γ.apos])
lemma fanfareFar :
 watt y E l r b (a/16) (tagFar H Γ).cost ≤
   Real.exp (-a*(b:ℝ)/3200)*fanbill a E c u l:=by
 refine (lit (tagFar H Γ) (fun _ h=>h.1) Γ.size.1 Γ.size.2
   (show 0<a/16 by linarith [Γ.apos]) Γ.Epay Γ.pays (by linarith)).trans ?_
 have c0:= (Shells.savings_nonneg _ (fun S=>(H.pass S).nonn) _).trans H.paid
 unfold fanbill; rw [mul_left_comm (Tallow ..)]
 apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.exp_pos _).le c0)
 apply Real.exp_monotone
 have v:(b:ℝ)≤400*(tenderb b:ℝ):=by
   exact_mod_cast show b≤400*tenderb b by unfold tenderb; have :=Γ.largeB; omega
 linarith only [mul_le_mul_of_nonneg_left v Γ.apos.le]

#print axioms fanfareLite
#print axioms fanfareFar

