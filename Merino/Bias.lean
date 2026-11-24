import Merino.Clasp
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered StressExchange Dial

lemma dg_lives (M:Finset I)(F:Op I)(v:∀ i j,F i j≠0→i∈M∧j∈M):
   Fock.Sector M false (dg F):=by
 unfold dg dyad
 refine Sector.sumS _ _ fun i _=> Sector.sumS _ _ fun j _=>?_
 by_cases e:F i j=0
 · rw [e,zero_smul]; exact .zero false
 obtain ⟨l,r⟩:=v _ _ e
 exact ((Sector.up _ l).mul (Sector.down _ r)).scale _

lemma sector_sub {M:Finset I}{F G:FC I}
    (t:Fock.Sector M false F)(p:Fock.Sector M false G):
    Fock.Sector M false (F-G):=by
 simpa [sub_eq_add_neg] using t.add (p.scale (-1))

-- The full W term in the bra-null payment really has short letter support.
private lemma wheel_fit (x:Site n)(i j:I)(u:millQ x i j≠0):
    node i.1.1=node x ∧ node j.1.1=node x:=by
 rw [millSt,Tye.stock,Matrix.diagonal_apply] at u
 split_ifs at u with h k
 · subst j; exact ⟨k,k⟩
 all_goals contradiction

lemma mode_in {x:Seat n}{S:Sa n}{i:I}(h:node i.1.1=x)(v:x∈S):
    i ∈ modesIn n S:=(mem_matterSet ..).mpr (mem_filter.mpr ⟨mem_univ _,h.symm ▸ v⟩)
lemma wheel_square (m:ℕ)(L:List Axis)(x:Site n)(i j:I) (S:Sa n)
    (g:∀ t:Site n,separation x t≤L.length*(3*m)→node t∈S)

    (h:squareSum millQ m L x i j ≠0):
    i∈modesIn n S∧j∈modesIn n S:=by
 induction L generalizing x with
 | nil =>
   have u:=g x (by simp)
   exact ⟨mode_in (wheel_fit _ _ _ h).1 u, mode_in (wheel_fit _ _ _ h).2 u⟩
 | cons a L ih =>
   rw [squareSum,stripSum,Matrix.sum_apply] at h
   obtain ⟨b,hb,t⟩:=exists_ne_zero_of_sum_ne_zero h
   refine ih _ ?_ t
   intro v w
   apply g
   rw [List.length_cons,Nat.succ_mul,add_comm]
   exact (separation_triangle ..).trans (Nat.add_le_add (leap_strip _ _ _ _ (mem_range.mp hb)) w)

namespace Spool.Hem
variable {a b d:ℝ}{K:Scree.Loom n}{p:BudgetPoint}{y:Spool n}
local notation "B"=>y.stepY
local notation "L"=>modesIn n (y.canvas p)
lemma seat_occupy (room:24*B≤p.B)(z:Orbit n):
    Fock.Sector L false (barS0 n B y.origin z):=by
 unfold barS0
 apply sector_sub _ (Sector.one.scale _)
 apply dg_lives
 intro i j t
 refine wheel_square B (List.ofFn (id:Axis→Axis)) y.origin i j _ ?_ t
 intro v l
 apply halo_spec.mpr
 have hi:separation y.origin v ≤ 4*(3*B):=l -- length defeq?
 refine ⟨y.post,mem_singleton_self _,?_⟩
 rw [post,Hove.ζdist]; omega

lemma a_jacket (h:Hem y K p a b d)(z:Orbit n)
    (i:Axis)(x:Site n)(l:separation y.origin x ≤ B):
    Fock.Sector L false (coverLine K p y.origin x (y.spin i) z):=by
 unfold coverLine houseK
 by_cases u:z.1∈pass p (node x)
 · have u':z∈pingMask p (offsetMask p.B x):=u
   rw [Set.indicator_of_mem u']; apply dg_lives
   intro e f v
   have he:=trunk_lives (trunk_go _ x (h.spurt i)) (h.skylight.slot z) _ _ v
   let t:=purse (p.B/10) (node x)
   have hv:t ⊆ y.canvas p:= inside.trans (fit l)
   exact ⟨mode_in rfl (hv he.1),mode_in rfl (hv he.2)⟩
 have u':z∉pingMask p (offsetMask p.B x):=u
 rw [Set.indicator_of_notMem u']; exact Sector.zero false

lemma occupies (h:Hem y K p a b d)(room:24*B≤p.B)(z:Orbit n)(q:ℂ):
    Fock.Sector L false (y.release K p q z):=by
 rw [release,Pi.smul_apply]
 apply Sector.scale
 unfold rift puffLine
 rw [Pi.add_apply]
 apply Sector.add
 · unfold houseK
   by_cases v:z∈pingMask p (offsetMask p.B y.origin)
   · rw [Set.indicator_of_mem v,Pi.sub_apply]; exact sector_sub (Sector.one.scale _) (seat_occupy room z)
   rw [Set.indicator_of_notMem v]; exact Sector.zero false
 unfold highLine; rw [Finset.sum_apply]; apply Sector.sumS
 intro i _; rw [Pi.sub_apply]
 exact sector_sub (h.a_jacket z i _ (stopBeam _ _ _).1) (h.a_jacket z i _ (stopBeam _ _ _).2)

lemma commute_apart {A N:Finset I}{F G:FC I}{v:Bool}
    (s:Fock.Sector A false F)(t:Fock.Sector N v G)(p:Disjoint A N): F*G=G*F:=by
 simpa [Sector.grainB] using s.apart t p

-- Can carry through arbitrary separated spectator insertions, either parity,
-- with all evaluations on exactly the same ket.
lemma have_y (h:Hem y K p a b d)(room:24*B≤p.B)(z:Orbit n)(q:ℂ)
    {A:Finset I}{T:FC I}{v:Bool}
    (t:Fock.Sector A v T)(l:Disjoint L A)
    (k:Phys n):
 inner ℂ (mateK n) (acts (T*y.opening K p q z.1) k)=
 inner ℂ (mateK n) (acts (T*y.release K p q z) k):=by
 have g:=((h.licensed q).loc.allV (z.1,z.1)).sector
 change Fock.Sector L false (y.opening K p q z.1) at g
 rw [←commute_apart g t l,←commute_apart (h.occupies room z q) t l,
    act_mul, (h.yoke q).inner_y z,act_mul]
end Spool.Hem
end YM.CF.Merino

