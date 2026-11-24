import Organdy.Ink
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Larva
open Filter Topology Metric Lattice Exterior Precision 
open Tulip Branch Cube Lat Tenant Drapes _root_.Zephyr.Chern

open scoped Matrix.Norms.L2Operator Matrix
attribute [local instance] opCStarAlgebra
local notation "G" => SU.group
variable {N m:Side}{d r:ℝ}


open Pressure Wilson Work.F03 Next.Rank.Spindle Payne
variable {n:Side}
abbrev Chip (n:Side):=Cell n × SU.group.ColorIndex
abbrev Tint:=PlaqAxes×SU.group.ColorIndex
abbrev dot (x:Chip n):Tint:=(x.1.2,x.2)
abbrev blush (x:Dir n)(i:Chip n):ℝ:=faceCurl i.1 x i.2

def stains (o:Site n)(k:ℕ) : Finset (Chip n) :=
 Finset.univ.filter (fun i=>separation o i.1.1 ≤ k)
lemma wet_iff {o:Site n}{k:ℕ}{i:Chip n}: i∈stains o k ↔ separation o i.1.1 ≤ k:=by simp [stains]

def nib (M:Finset (Chip n)):Dir n →ₗ[ℝ] Ink.Paint (Chip n) where
 toFun x:= WithLp.toLp 2 (fun i=>if i∈ M then blush x i else 0)
 map_add' x y:=by
   ext i
   simp only [PiLp.add_apply]
   split
   · change (Exterior.d 1 n *ᵥ parts SU.group 1 (x+y) i.2) (i.1.1,plaquette i.1.2)= _
     rw [show parts SU.group 1 (x+y) i.2= parts SU.group 1 x i.2 + parts SU.group 1 y i.2 from rfl,
         Matrix.mulVec_add]; rfl
   · symm;apply add_zero
 map_smul' c x:=by
   ext i
   simp only [PiLp.smul_apply,RingHom.id_apply]
   split
   · change (Exterior.d 1 n *ᵥ parts SU.group 1 (c•x) i.2) (i.1.1,plaquette i.1.2)= _

     rw [show parts SU.group 1 (c•x) i.2=c • parts SU.group 1 x i.2 from rfl,
         Matrix.mulVec_smul]; rfl
   · symm;apply smul_zero
lemma dab {o:Site n}{k:ℕ}(x:Dir n)(i:Cell n)(h:separation o i.1≤k):
  ‖faceCurl i x‖ ≤ ‖nib (stains o k) x‖:=by
 let b:=nib (stains o k) x
 have e(j:SU.group.ColorIndex):b (i,j)=faceCurl i x j:=if_pos (wet_iff.mpr h)
 rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
 apply Real.sqrt_le_sqrt
 rw [Fintype.sum_prod_type]
 apply le_trans _ (Finset.single_le_sum (a:=i)
   (fun _ _=>Finset.sum_nonneg fun _ _=>sq_nonneg _) (Finset.mem_univ i))
 exact Finset.sum_le_sum fun j _=> le_of_eq (congrArg (fun a:ℝ=>‖a‖^2) (e j).symm)

abbrev locale (k:ℕ):ℝ:=16*((k:ℝ)+1)^4*Fintype.card Tint

open Finset in
lemma count (o:Site n)(k:ℕ):
 ((stains o k).card:ℝ) ≤ locale k:=by
 let B:=bay (terr n) o k
 let V:=B ×ˢ (univ:Finset Tint)
 have h:(stains o k).card ≤ V.card:=by
    apply card_le_card_of_injOn (f:=fun (x:Chip n)=>(x.1.1,dot x))
    · intro i g;exact mem_product.mpr ⟨(bay_mem _).mpr (wet_iff.mp g),mem_univ _⟩
    rintro ⟨⟨i,b⟩,a⟩ _ ⟨⟨j,c⟩,d⟩ _
    simp [dot, and_assoc]
 rw [show V.card=B.card*Fintype.card Tint by simp [V]] at h
 apply le_trans _ (mul_le_mul_of_nonneg_right (Tenant.reach o k) (Nat.cast_nonneg (Fintype.card Tint)))
 exact_mod_cast h

lemma fragile {S:Band N}{F:Oil N}{C:Toll (Single N)}
  {k:ℕ}{o:Site (More N)}
  (h:Piece d S C F)(R:Rules G)(t:Spool d r)
  (e:2*(k+1)<(More N).val)
  (f:∀ i∈leaks S,separation o i.1≤k):
  ∃ A:Ink (Chip (More N)),
    A.Sym ∧ A.Within (stains o (k+1)) ∧
    A.qty ≤ locale (k+1)^2*(2*scale k r (ledgerV C)) ∧
    ∀ x, poem F x=A.gilt (blush x) :=by
 let W:=stains o (k+1)
 obtain ⟨Q,u,v⟩:=poem_bend h t
 let p:=scaleN k t.1.le (ledgerT h.toTicket).1
 have y(x):‖Q x x‖ ≤ scale k r (ledgerV C)*‖nib W x‖^2 :=by
    rw [←u]
    exact ordained h R t e f x _ (norm_nonneg _) (fun i a=>dab x i a)

 obtain ⟨A,l,j,b,a⟩:=Ink.sepia Q (nib W) p v y W (fun x i t=>if_neg t)
 refine ⟨A,l,j,b.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (count ..) 2)
     (mul_nonneg two_pos.le p)),fun x=>?_⟩
 rw [u,a]; exact Ink.same j (fun _ w=> if_pos w)
