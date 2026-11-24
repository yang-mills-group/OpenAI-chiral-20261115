import SatinThinLittle
import Organdy.Virgin
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste.Clock
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye CF.Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open Buffered.Afterglow
open Next.Rank.Thirst
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m:Side}{j r p d t:ℕ}{M:Tulip.Male}{ε ξ σ C D:ℝ}
namespace Hookah.Rake
open Regis.Head Etch Regis.Head.Garland
open scoped Classical
open Scree

open Organdy Optic Scree Push.Local
-- Bose probes
variable {W:Pane N→ℂ} {z o: Seat N} {s:Signed}{w : ℕ} {x a:ℝ}


abbrev markPair (x:ℝ)(W:Pane N→ℂ)(z:Seat N):Mark N:=
 fun U=>cistern x W z 1 0 U.1 • 1
def pom(b:Bool)(x:ℂ):ℂ:=if b then star x else x
def pop (x:ℝ)(W:Pane N→ℂ)(z:Seat N)(a:ℝ)(s:Signed)(o:Seat N)(b:Bool)(U:Pane N):ℂ:=
  1+(a:ℂ)*pom b (cistern x W z s o U)
def bootM(x:ℝ)(W:Pane N→ℂ)(z:Seat N)(a:ℝ)(s:Signed)(o:Seat N)(b:Bool) :Mark N:=
 fun U=>pop x W z a s o b U.1 • 1

structure Broach (W:Pane N→ℂ)(z:Seat N)(w:ℕ)(x a:ℝ)(A:Hookah N):Prop where
 owner : AtSupport false A.S A.x
 income : ∃ (s:Signed)(o:Seat N)(b:Bool),A.x=bootM x W z a s o b ∧
     Lattice.halo (w+2) {o,affine s o z} ⊆ A.S

variable {A:Hookah N}
lemma Broach.reflect (p:Broach W z w x a A)(i:Axis)(d:ℤ) :
    Broach W z w x a (A.twistL i d):=by
 refine ⟨p.owner.refl i d,?_⟩
 obtain ⟨s,o,b,h,j⟩:=p.income; let q:= (Signed.mirror i); let c:Seat N:=wrap (More N) (2 • (d • step i))
 refine ⟨q*s,affine q c o,!b,?_,?_⟩
 · change reflMark i d A.x=_; rw [h]; funext U
   simp only [reflMark, bootM,pop,theta_smul,theta_one,show (reflFields i d U).1= fling i d N U.1 from rfl,fling_eq,cistern_swing,star_add,star_one,star_mul',Complex.star_def,Complex.conj_ofReal]
   cases b <;> simp [pom,q,c,two_mul,two_smul]
 rw [inlay]
 have hx:= image_subset_image (f:=⇑(turnSites q c)) j
 have p' : (Lattice.halo (w+2) {o,affine s o z}).image (turnSites q c)=
    Lattice.halo (w+2) {affine q c o,affine q c (affine s o z)}:=by
   ext u; obtain ⟨i',rfl⟩:=(turnSites q c).surjective u
   change _ ↔ _ ∈ Lattice.halo _ {(turnSites q c) o,(turnSites q c) (affine s o z)}
   simp [halo_spec,(turnSites q c).injective.eq_iff]
 rw [p'] at hx
 exact hx

variable {t':ℝ}
variable {L J:List (Hookah N)}
structure Sown (W:Pane N→ℂ)(z:Seat N)(w:ℕ)(x t':ℝ)(p:ℕ)(L:List (Hookah N)):Prop where
 core (A:Hookah N)(v:A∈L):Broach W z w x t' A
 annex:L.Pairwise (fun i z=>Distant (p+1) i.S z.S)
variable (u:Sown W z w x t' p L)
namespace Sown
include u
lemma away(i:Axis)(z1:ℤ): Sown W z w x t' p (L.map (fun v=> v.twistL i z1)):=by
 refine ⟨fun A w=>?_, List.pairwise_map.mpr (u.annex.imp fun g=> sparse_face g i z1)⟩; obtain ⟨k,ψ,rfl⟩:= List.mem_map.mp w; exact (u.core k ψ).reflect i z1
lemma tack (v:Sown W z w x t' p J)(h:Disjoint (Broad p L) (Broad p J)): Sown W z w x t' p (L++J):=⟨fun i g=>(List.mem_append.mp g).elim (u.core i) (v.core i), List.pairwise_append.mpr ⟨u.annex,v.annex,fun a e b g=>SparseLock (h.mono (Broad_x p L a e) (Broad_x p J b g))⟩⟩
end Sown
include u in
lemma Sown.occupy : AtSupport false (Broad p L) (buffet L):=by
 induction L with
 | nil=>exact (show buffet ([]:List (Hookah N))=1 from buffet_empty) ▸ AtSupport.oneM _ -- rewrite direction
 | cons i L ih=>
   let hA:= u.core i List.mem_cons_self
   rw [buffet_more,Broad_more]; exact (hA.owner.mono (subset_trans (fun x v=> halo_spec.mpr ⟨x,v,(separation_self _).le.trans (Nat.zero_le _)⟩) subset_union_left)).mulM ((ih ⟨fun k v=>u.core k (List.mem_cons_of_mem _ v), (List.pairwise_cons.mp u.annex).2⟩).mono subset_union_right)
variable {r₀ p₀ B l:ℕ}{ν:Mark N→ℂ}(wc:Twosome K N ν)
lemma Sown.one (h:Broach W z w x t' A): Sown W z w x t' p [A]:=⟨fun i hi=> (List.mem_singleton.mp hi).symm ▸ h,List.pairwise_singleton ..⟩
include wc
lemma stance (g:N=K.c m) (A:List (Hookah N)) (i:Axis)
    (f:Sown W z w x t' p₀ A) (q:cows i (Broad p₀ A) B)(Vv:2^l*(B+addgap K)≤ N.val) :
    ∃ V:List (Hookah N),Sown W z w x t' p₀ V ∧ V.length=2^l*A.length ∧ ‖ν (buffet A)‖^(2^l)≤ ‖ν (buffet V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (Broad p₀ A) s → cows a (Broad p₀ V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ N.val:= Vv.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z1,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z1
    let U:= A.map fun a=> a.twistL i s; let WW:= U++A; have h'': Broad p₀ WW=hyphen i s (Broad p₀ A)∪ Broad p₀ A:=by unfold WW U; rw [Broad_append,Broad_turn]; -- fix rfl
    have hp:Broad p₀ A⊆ band N i s K.ℓ:=p
    have hx: Sown W z w x t' p₀ WW := (f.away i s).tack f (by rw [Broad_turn]; exact west K i s _ hp)
    have hw:= wc i z1 (buffet A) (f.occupy.mono hp)
    obtain ⟨Y,a',b,r,g'⟩:= ih WW hx (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at Vv; exact Vv.trans' (le_of_eq (by ring)))
    refine ⟨Y,a',?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold WW U; rw [List.length_append,List.length_map]; ring -- WW/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z1) (buffet A)*buffet A=buffet WW:=by unfold WW U; rw [buffet_tack,buffet_turn] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma scattering (g:N=K.c m)(Vv:2^l*(B+addgap K)≤ N.val)(S:Finset Axis) (A:List (Hookah N))(f:Sown W z w x t' p₀ A)
    (p:∀ a∈S,cows a (Broad p₀ A) B) : ∃ U:List (Hookah N), Sown W z w x t' p₀ U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (buffet A)‖^((2^l)^S.card) ≤ ‖ν (buffet U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,a₁,b,vL⟩:= stance (ν:=ν) wc g A i f (p i (mem_insert_self ..)) Vv
    obtain ⟨Z,gX,e,l'⟩:= ih U hU (fun s v=> vL s (fun h=>x (h ▸ v)) _ (p s (mem_insert_of_mem v))) -- extras
    rw [card_insert_of_notMem x,pow_succ']; refine ⟨Z,gX,?_,?_⟩
    · rw [e,a₁]; ring
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) b _).trans l'
omit wc
private lemma goldilock {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
include wc
lemma trifecta (g:N=K.c m)(Vv:B+addgap K≤ N.val)(A:Hookah N)(f:Broach W z w x t' A)(p:∀ i,cows i (Lattice.halo p₀ A.S) B) :
    ∃ U: List (Hookah N), Sown W z w x t' p₀ U ∧ 0<U.length ∧ U.length ≤ (More N).val^4 ∧
       (More N).val^4 ≤ U.length*(4*(B+addgap K))^4 ∧ ‖ν A.x‖^U.length≤ ‖ν (buffet U)‖:=by
 obtain ⟨k',a₁,l⟩:= goldilock (x:=N.val) (show 0 < B+addgap K from Nat.add_pos_right _ addgap_pos) Vv
 obtain ⟨U,f',H,hY⟩:= scattering (ν:=ν) wc g a₁ univ [A] (Sown.one f) (fun i b=>by simpa [Broad_more] using p i) -- whereF
 have hw:(univ: Finset Axis).card=4:=by simp [Axis]
 have hp:U.length=(2^k')^4:= by simpa [hw] using H
 refine ⟨U,f',?_,?_,?_,?_⟩
 · rw [hp]; positivity
 · change _ ≤ (N.val*2)^4; rw [hp]; apply pow_le_pow_left'; have hq:= a₁.trans' (Nat.le_mul_of_pos_right (2^k') (Nat.add_pos_right _ (show 0 < addgap K from addgap_pos))); omega
 · rw [hp,← mul_pow]; apply pow_le_pow_left'; change N.val*2 ≤_; apply le_trans (Nat.mul_le_mul_right 2 l); exact le_of_eq (by ring)
 rw [hp]; simpa only [hw,buffet_more,buffet_empty,mul_one] using hY
omit wc
