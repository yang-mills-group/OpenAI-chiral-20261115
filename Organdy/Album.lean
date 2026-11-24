import Organdy.Dry
import YM.SU5.Exchange.Pipe.Latch
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


open Swell Payne Wilson Next.Rank.Spindle Scree
open Finset

-- charge all at same k. compare pass reading: `V` is the reconstructed
-- background. Doesn't insist U∈Tiny.
abbrev Dye (N:Side) := Ink (Chip (More N))
abbrev lyre (P:Oil N)(A:Dye N)(x:Dir (More N)): Fin 3 → ℂ:=
 ![sketch P 0,0,A.gilt (blush x)]

structure Album (d r D τ:ℝ)(k:ℕ)(o:Site (More N))(P:Oil N)(A:Dye N):Prop where
  pal: A.Sym
  pin: A.Within (stains o k)
  pie: A.qty ≤ D
  pet (x:Dir (More N)):Bloom (maline (sketch P) 0 x) (lyre P A x)
  pen (x:Dir (More N)):
    ‖x‖ < r →
    ‖sketch P x - sketch P 0 - A.gilt (blush x)‖ ≤ D*‖x‖^3
  pk (V U:Config SU.group (More N)):
    Tiny d V →
    Agrees (halo k {o}) V U →
    Cheap o k U τ →
    ‖story P V-sketch P 0‖ ≤D*τ^2

variable {τ a b D :ℝ}{P:Oil N}{A:Dye N}
variable {k:ℕ}{o:Site (More N)}{R:Rules G}
-- Agrees in YM.CF.Scree? 

structure Sky (n:Side)(d r a D τ:ℝ)(k:ℕ)(R:Rules G) : Prop where
  flow : Spool d r
  estate : 2*(k+1)<n.val
  cost_pos:0≤D
  price(u:ℕ): dust r u ≤ D * Real.exp (a*u)
  threshold :0≤τ
  width : stretch k*τ < min R.c r

lemma elapse {S:Band N}{C:Toll (Single N)}
   (h:Piece d S C P)(p:o∈ S)(q:S.card<k)(e:C≠0)
   (t:Sky (More N) d r a D τ k R):
 ∃ A, Album d r (D*(Branch.rent a S*ledgerV C)) τ k o P A:=by
 have B:=f_then h e
 have m(y)(u:y∈ S): separation o y ≤ S.card:=(B.lim _ p _ u).le
 have x(i)(v:i∈leaks S):separation o i.1 ≤ S.card := m _ (mem_filter.mp v).2.1
 have side:=t.estate
 obtain ⟨A,l,j,w,y⟩:=fragile h R t.flow (show 2*(S.card+1)<_ from by omega) x
 have mono : stains o (S.card+1) ⊆ stains o k:= fun i g=>wet_iff.mpr ((wet_iff.mp g).trans q)

 have v:0≤ledgerV C:=(ledgerT h.toTicket).1
 have z:0≤ sweets r:=sweets_nonneg t.flow.1.le
 have g:=scaleN S.card t.flow.1.le v

 let T:=(locale (S.card+1))^2*(2*scale S.card r (ledgerV C))
 have pn:0≤T:=by unfold T; positivity
 have price:T + scale S.card r (ledgerV C) + sweets r * ledgerV C ≤ D*(Branch.rent a S*ledgerV C):=by
   rw [←mul_assoc]
   apply le_trans _ (mul_le_mul_of_nonneg_right (t.price S.card) v)
   unfold T dust scale
   exact le_of_eq (by ring)
 have sw:=mul_nonneg z v
 refine ⟨A,l,Ink.within_mono j mono,w.trans (by linarith), fun X=>by
    have b:=bloom_paid h t.flow X
    rw [y] at b
    exact b,fun X b=>?_,?_⟩
 · rw [←y]
   exact (rhyme h t.flow b).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
 intro V U i f n
 apply le_trans _ (mul_le_mul_of_nonneg_right (show scale S.card r (ledgerV C) ≤ D*(Branch.rent a S*ledgerV C) by linarith) (sq_nonneg τ))
 have l(Z)(p:Z∈S):Z∈halo k {o}:= halo_spec.mpr ⟨o,mem_singleton_self _,(m _ p).trans q.le⟩
 exact warden h R t.flow (by omega : 2*(S.card+1)<(More N).val) x i
    (fun j p=> f j (l _ (mem_filter.mp p).2.1) (l _ (mem_filter.mp p).2.2))
    t.threshold ((mul_le_mul_of_nonneg_right (stretchMono q.le) t.threshold).trans_lt t.width)
    (U:=U) (fun i u=> n i (u.trans (by omega)))

variable {J:Type}[Fintype J][DecidableEq J]{s:Finset J}
 {F:J→Oil N}{Q:J→Dye N} {c:J→ℝ}

lemma sheaf (t:Spool d r)
  (p:∀ j∈s, Album d r (c j) τ k o (F j) (Q j))
  (g:(∑j∈s,c j)≤b)
  (l:∀ U:Config SU.group (More N), Tiny d U→ story P U=∑j∈s, story (F j) U):
  Album d r b τ k o P (∑j∈s,Q j):=by
 let A:=∑ j∈s,Q j
 have rem {x:Dir (More N)} (h:‖x‖<r):
  sketch P x=∑ j∈s, sketch (F j) x:=l _ (pinpoint t (h.trans (by linarith [t.1])))
 have c0:=rem (x:=0) (by rw [norm_zero]; exact t.1)
 refine ⟨Ink.sym_sum s Q (fun j m=>(p j m).pal), Ink.within_sum s Q (fun j m=>(p j m).pin),
   (Ink.qty_sum s Q).trans ((sum_le_sum (fun j m=>(p j m).pie)).trans g),?_,?_,?_⟩
 · intro x
   have e: maline (sketch P) 0 x=ᶠ[𝓝 0] fun u=>∑ j∈s,maline (sketch (F j)) 0 x u:=by
     have i:Continuous (fun u:ℝ=> ‖(0:Dir (More N))+u•x‖):= by fun_prop
     filter_upwards [i.continuousAt.eventually (gt_mem_nhds
       (show ‖0+(0:ℝ)•x‖<r by simpa using t.1))] with u v
     exact rem v

   rw [show lyre P (∑j∈s,Q j) x=∑ j∈s,lyre (F j) (Q j) x from ?_]
   · exact (Bloom.sum s (fun j m=>(p j m).pet x)).congr e
   dsimp only [lyre]
   funext i
   rw [Finset.sum_apply];fin_cases i
   · exact c0
   · simp
   · exact Ink.gilt_sum s Q (blush x)
 · intro x u
   rw [rem u, c0, Ink.gilt_sum,←sum_sub_distrib,←sum_sub_distrib]
   refine (norm_sum_le ..).trans ((sum_le_sum (fun j m=>(p j m).pen x u)).trans ?_)
   rw [←sum_mul];exact mul_le_mul_of_nonneg_right g (by positivity)
 intro V U u m v
 rw [l V u,c0,←sum_sub_distrib]
 refine (norm_sum_le ..).trans ((sum_le_sum (fun j a=>(p j a).pk V U u m v)).trans ?_)
 rw [←sum_mul];exact mul_le_mul_of_nonneg_right g (sq_nonneg τ)

lemma pages (h:Trunk o P k a b d)
 (t:Sky (More N) d r a D τ k R):∃ A, Album d r (D*b) τ k o P A:=by
 classical
 obtain ⟨F,C,L,p,v,g⟩:=h.home
 let s:Finset (Band N):=univ.filter (fun j=>C j≠0)
 let Y:Band N→Oil N:=fun S y=> if u:y∈Openc _ d then F S ⟨y,u⟩ else 0
 have z (S:Band N) : F S=fun j=> Y S j.val:=funext fun j=>by simp [Y,j.property]
 have m(S):Piece d S (C S) (Y S):=by
   have a:=L S;rw [z] at a;exact a
 have w(U)(u:Tiny d U):story P U=∑j∈s,story (Y j) U:=by
   rw [story,g ⟨profile U,u⟩, Matrix.trace_sum]
   calc
     _ = ∑ j:Band N,story (Y j) U := sum_congr rfl (fun j _=>congrArg Matrix.trace (congrFun (z j) ⟨_,u⟩))
     _ = _:= by
       symm
       apply sum_subset (subset_univ _)
       intro j _ b
       have y:C j=0:=not_not.mp (fun a=>b (mem_filter.mpr ⟨mem_univ _,a⟩))
       exact norm_le_zero_iff.mp ((show ‖story (Y j) U‖≤ledgerV (C j) from
          (ledgerT (m j).toTicket).norms ⟨_,u⟩).trans (by simp [y,ledgerV]))

 let c:Band N→ℝ:=fun S=>D*(Branch.rent a S*ledgerV (C S))
 have U:∀ S∈s,∃ A, Album d r (c S) τ k o (Y S) A:=by
    intro S i; have e:C S≠0:= (mem_filter.mp i).2
    exact elapse (m S) (p _ e).1 (p _ e).2 e t
 choose! A u using U
 refine ⟨_, sheaf t.flow u ?_ w⟩
 unfold c
 refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>mul_nonneg t.cost_pos
      (mul_nonneg (rent_pos _ _).le (ledgerT (m i).toTicket).1))).trans ?_
 rw [←mul_sum]
 exact mul_le_mul_of_nonneg_left v t.cost_pos
