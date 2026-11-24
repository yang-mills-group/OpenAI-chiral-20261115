import Gingham.Ruff.Kite
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

abbrev Dahlia (x: Site N)(r s:ℕ):=
 Jabot (faerie (Tenant.terr (More N)) (node x) r s)

variable {a c e:ℝ} {r:ℕ}{f g:Chin N→OP N}
variable {z u y:Site N}
lemma dahlia (p:Spotlit u a c f e)(h:separation y u ≤ r):
    Dahlia y (2*r) 1 a c f e :=
  p.shape (fun S _ _ b _ _ t v hv=>by
    change separation _ _ ≤ _
    have hx:=separation_triangle (node y) (node u) v
    rw [iguana] at hx
    have hq:separation (node u) v < S.card:= b.lim _ t _ hv
    omega)

def struts (y:Site N)(s:ℕ):=Dahlia y 0 s

lemma swannery (z u y:Site N)(ha:0≤a)(h:Solo a c f e)(g':Solo a c g e)
    (l:separation y u ≤ 4*pdist z):
    struts y 5 (a/2) (Real.exp (-(a*(pdist z:ℝ))) * dovecote a c)
     (firstmate f g z u) e:=by
  have p:=
     (feathers2 u ha h g').streami (node (u+z))
  -- strip stage e vs WW strip stage 0 defeq
  have hm (S) (b:Grove (Tenant.terr (More N)) S)
      (t:node (u+z)∈S ∧ node u∈S): 2*pdist z < S.card:=by


    have q: separation (node (u+z)) (node u) < S.card:=b.lim _ t.1 _ t.2
    rwa [iguana, separation, add_sub_cancel_left] at q

  refine (Brooch.take (m:=a/2) (Real.exp (-(a*(pdist z:ℝ)))) (Real.exp_pos _).le ?_ p).shape ?_
  · intro S _ _ b _ _ t
    have hv:2*(pdist z:ℝ)<S.card:=by exact_mod_cast hm S b t
    rw [Branch.rent,Branch.rent,←Real.exp_add]
    exact Real.exp_monotone (by nlinarith only[mul_le_mul_of_nonneg_left hv.le ha])
  · -- order goals?
    intro S i j b _ _ t v hv
    change separation _ _≤ _
    have hx:=separation_triangle (node y) (node u) v
    rw [iguana] at hx
    have hh:separation (node u) v<S.card:=b.lim _ t.2 _ hv
    have := hm S b t
    omega

lemma lance (d:Step): pdist (d.vec : Site N) ≤1:=by
  unfold Lattice.Step.vec; split
  · rw [pdist_neg];exact pdist_step _
  exact pdist_step _
lemma reverseSep (x q:Site N): separation x (x-q)=pdist q:=by rw [separation,sub_sub_cancel]



lemma palisade (z:Site N)(q:Site N)(w:Walk)(ha:0≤a)(h:Solo a c f e)(g':Solo a c g e)
    (y:Site N)(i:Axis)(l:pdist q+w.length ≤ 4*pdist z):
    struts y 5 (a/2)
    ((w.length:ℝ) * (Real.exp (-(a*(pdist z:ℝ))) * dovecote a c))
    (fun p=>sail (fun u=>firstmate f g z u p) i q y w) e:=by
  have hc:0 ≤ dovecote a c:= (feathers2 y ha h g').positive
  induction w generalizing q with
  | nil => simp only [sail,List.length_nil,Nat.cast_zero, zero_mul]; exact Brooch.free
  | cons d w ih =>
    have t:pdist (q+d.vec)+w.length ≤4*pdist z:=by
      simp only [List.length_cons] at l
      have h₁:=pdist_triangle q d.vec; have h₂:=lance (N:=N) d; omega
    have X:struts y 5 (a/2)
          (Real.exp (-(a*(pdist z:ℝ))) * dovecote a c)
          (fun p=>foremast (fun u=>firstmate f g z u p) d q y i) e:=by
      unfold foremast
      by_cases b:i=d.dir
      · simp only [if_pos b]
        by_cases k:d.neg=true
        · simp only [if_pos k]
          exact (swannery z _ _ ha h g' (by rw [reverseSep]; omega)).minus


        simp only [if_neg k]; exact swannery z _ _ ha h g' (by rw [reverseSep]; omega)
      simp only [if_neg b]
      exact Brooch.free.books (by positivity)

    rw [List.length_cons, Nat.cast_add, Nat.cast_one,add_mul,one_mul,add_comm]
    exact X.plus (ih _ t)


def aviary (a c:ℝ):= 4*(16*primaries 5 a)* dovecote a c

lemma moorhen (ha:0<a)(h: Solo a c f e)(g':Solo a c g e)
    (i:Axis)(y:Site N): struts y 5 (a/2) (aviary a c) (sprit f g i y) e:=by
  let F(z:Site N):=Real.exp (-(a*(pdist z:ℝ)))
  let k(z:Site N):= ((turncoat z).length:ℝ) * (F z * dovecote a c)
  refine (Brooch.sumK univ k
       (fun z p=>sail (fun u=>firstmate f g z u p.val) i 0 y (turncoat z))
       (b:=forum N e) (s:=bail N e) (t:=bail N e)
       (fun z _=>palisade z 0 (turncoat z) ha.le h g' y i (by simpa [show pdist (0:Site N)=0 from by simp [Lattice.pdist,Lattice.lift]] using turncoat_size z))).books ?_
  have hp:∑ z:Site N,((pdist z:ℝ)+1)* F z ≤ 16*primaries 5 a := by
    have v:= fly (@pdist N) ha (r:=16) (by norm_num) 4 1
         (fun b=> (Nat.cast_le.mpr (card_le_card
              (t:=bay (Tenant.terr _) 0 b) (fun z h=>by
                 apply (bay_mem b).mpr
                 change separation 0 _ ≤ b
                 rw [separation_comm, separation, sub_zero, (mem_filter.mp h).2]))).trans
                       (Tenant.reach _ _))
    simp only [pow_one, neg_mul] at v ⊢
    simpa [F] using v


  have hc:0 ≤ dovecote a c:= (feathers2 y ha.le h g').positive
  apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
       (show 0 ≤ (4:ℝ) from by norm_num)) hc)
  rw [mul_sum,sum_mul]
  apply sum_le_sum
  intro z _
  have hx:((turncoat z).length:ℝ) ≤ 4*(pdist z:ℝ):= by exact_mod_cast turncoat_size z
  change _ * (_ * _) ≤ _ * _
  rw [←mul_assoc _ (F z),←mul_assoc 4]
  -- (4*((pdist+1)*F))*c, rw 2nd maybe rewrites 4 into 4*(pd...)??
  apply mul_le_mul_of_nonneg_right _ hc
  exact mul_le_mul_of_nonneg_right (hx.trans (by linarith)) (Real.exp_pos _).le

