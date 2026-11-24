import SatinThinPark
import SatinThinIncense
import SatinThinCircuitry
import YM.SU5.Regis.Visitations
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
namespace Hookah.Blaze
open Regis.Head Etch Regis.Head.Garland
open scoped Classical
open Scree
variable {I:Type*}[Fintype I]
/-- duplicate the CONVENTION with clip-edge strict guard! for Tour.Expose tall clocks.-/
def kris (A:PlaqAxes→ℝ)(ρ t:ℝ)(s:Signed)(o: Seat N)(U: Pane N):ℝ:= let V:= Lattice.pull s o U; if Scree.pingS t (Lattice.halo 10 {(0:Seat N)}) V then petalWorth A ρ V else 0 -- pull namespace Lattice? from Lattice
lemma kris_cost {A:PlaqAxes→ℝ}{p:BudgetPoint}{s:Signed}{o:Seat N}{ρ:ℝ}{U:Pane N}: |kris A ρ p.threshold s o U|≤ Etch.costG A p.threshold ρ:=by
 unfold kris; dsimp only; split; next h=>
    have hx:= Etch.costG_le (P:=p) A s o (U:=U) (x:=ρ); unfold Etch.garland at hx; rw [RG.masked_eq _ _ _ _ (Scree.ping_le h)] at hx; exact hx
 rw [abs_zero]; unfold costG meritG; positivity
variable (z:PlaqAxes→ℝ)(E:Tour I (More N))(A:Hookah N)(ρ:ℝ)
def silk (t:ℝ)(U:Pane N):ℝ:=∏ i:I, kris z ρ t (E.orient i) (E.loc i) U
def bootF(t:ℝ)(τ:ℂ)(U:Fields N): FC (Single N):= (1+τ*(silk z E ρ t U.1:ℝ)) • 1
lemma silk_moves (s:Signed)(b:Seat N)(v:ℝ)(U:Pane N): silk z E ρ v (Lattice.pull s b U)=silk z (E.moves s b) ρ v U:=by unfold silk kris; dsimp only; simp_rw [pull_pull]; rfl
lemma silk_price (p:BudgetPoint)(U:Pane N): |silk z E ρ p.threshold U|≤ costG z p.threshold ρ^Fintype.card I:=by unfold silk; rw [abs_prod]; refine (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>kris_cost)).trans_eq ?_; rw [prod_const,card_univ]
-- a.e. transform 
lemma silk_warm {t:ℝ}(h: CF.Rue.IsleB SU.group t): (silk z E ρ t)=ᵐ[prior SU.group (More N)] E.exhibit z ρ t:=by
 have he(i:I): kris z ρ t (E.orient i) (E.loc i)=ᵐ[prior SU.group (More N)] Etch.garland z ρ t (E.orient i) (E.loc i):=by
    filter_upwards [(prior_pull (E.orient i) (E.loc i)).quasiMeasurePreserving.ae (h _)] with x p
    unfold kris Etch.garland; dsimp only; split; next k=> exact (RG.masked_eq _ _ _ _ (Scree.ping_le k)).symm
    next k=> exact (RG.masked_ne _ _ _ _ (fun t=>k ((CF.Rue.shoreK _ _ p _).mp t))).symm
 filter_upwards [Filter.eventually_all.mpr he] with x p; exact Finset.prod_congr rfl fun i _=> p i
-- duplication by Vote (Adapt Visitations Heat)
structure Vote (z:PlaqAxes→ℝ)(E:Tour I (More N))(ρ t:ℝ)(τ:ℂ)(A:Hookah N) :Prop where
 owner : AtSupport false A.S A.x
 slotT : A.o∈A.S
 issued : ∃ (s:Signed)(o:Seat N)(a:ℂ),(a=τ∨a=star τ) ∧ A.x=bootF z (E.moves s o) ρ t a ∧ (∀ j:I,(E.moves s o).loc j∈A.S)
variable {z A E ρ}{τ:ℂ}
lemma Vote.reflect (p:Vote z E ρ ε τ A)(i:Axis)(a:ℤ) : Vote z E ρ ε τ (A.twistL i a):=by
 refine ⟨p.owner.refl i a, mem_image_of_mem _ p.slotT,?_⟩; obtain ⟨t,o,V,h,x,s0⟩:=p.issued; let q:= (Signed.mirror i); let b:Seat N:=wrap (More N) (2 • (a • step i))
 refine ⟨q*t,affine q b o,star V,(h.elim (fun h=>h ▸ Or.inr rfl) (fun h=> Or.inl (by rw [h,star_star]))),?_,fun j=>?_⟩ <;> rw [←Tour.rules]
 · change reflMark i a A.x=_; rw [x]; funext U; unfold reflMark bootF; rw [theta_smul,theta_one,show (reflFields i a U).1= fling i a N U.1 from rfl,fling_eq,silk_moves]; rw [star_add,star_one,star_mul',Complex.star_def,Complex.conj_ofReal]; try rfl
 exact mem_image_of_mem _ (s0 j)
variable {L J:List (Hookah N)}
structure Sown (z:PlaqAxes→ℝ)(E:Tour I (More N))(ρ ε:ℝ)(τ:ℂ)(p:ℕ)(L:List (Hookah N)):Prop where
 core (A:Hookah N)(v:A∈L):Vote z E ρ ε τ A
 annex:L.Pairwise (fun i z=>Distant (p+1) i.S z.S)
variable (u:Sown z E ρ ε τ p L)
namespace Sown
include u
lemma away(i:Axis)(z1:ℤ): Sown z E ρ ε τ p (L.map (fun v=> v.twistL i z1)):=by
 refine ⟨fun A w=>?_, List.pairwise_map.mpr (u.annex.imp fun g=> sparse_face g i z1)⟩; obtain ⟨k,ψ,rfl⟩:= List.mem_map.mp w; exact (u.core k ψ).reflect i z1
lemma tack (v:Sown z E ρ ε τ p J)(h:Disjoint (Broad p L) (Broad p J)): Sown z E ρ ε τ p (L++J):=⟨fun i g=>(List.mem_append.mp g).elim (u.core i) (v.core i), List.pairwise_append.mpr ⟨u.annex,v.annex,fun a e b g=>SparseLock (h.mono (Broad_x p L a e) (Broad_x p J b g))⟩⟩
end Sown
include u in
lemma Sown.occupy : AtSupport false (Broad p L) (buffet L):=by
 induction L with
 | nil=>exact (show buffet ([]:List (Hookah N))=1 from buffet_empty) ▸ AtSupport.oneM _ -- rewrite direction
 | cons i L ih=>
   let hA:= u.core i List.mem_cons_self
   rw [buffet_more,Broad_more]; exact (hA.owner.mono (subset_trans (fun x v=> halo_spec.mpr ⟨x,v,(separation_self _).le.trans (Nat.zero_le _)⟩) subset_union_left)).mulM ((ih ⟨fun k v=>u.core k (List.mem_cons_of_mem _ v), (List.pairwise_cons.mp u.annex).2⟩).mono subset_union_right)
variable {r₀ p₀ B l:ℕ}{ν:Mark N→ℂ}(a:Twosome K N ν)
lemma Sown.one (h:Vote z E ρ ε τ A): Sown z E ρ ε τ p [A]:=⟨fun i hi=> (List.mem_singleton.mp hi).symm ▸ h,List.pairwise_singleton ..⟩
include a
lemma stance (g:N=K.c m) (A:List (Hookah N)) (i:Axis)
    (f:Sown z E ρ ε τ p₀ A) (q:cows i (Broad p₀ A) B)(Vv:2^l*(B+addgap K)≤ N.val) :
    ∃ V:List (Hookah N),Sown z E ρ ε τ p₀ V ∧ V.length=2^l*A.length ∧ ‖ν (buffet A)‖^(2^l)≤ ‖ν (buffet V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (Broad p₀ A) s → cows a (Broad p₀ V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ N.val:= Vv.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z1,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z1
    let U:= A.map fun a=> a.twistL i s; let W:= U++A; have h'': Broad p₀ W=hyphen i s (Broad p₀ A)∪ Broad p₀ A:=by unfold W U; rw [Broad_append,Broad_turn]; -- fix rfl
    have hp:Broad p₀ A⊆ band N i s K.ℓ:=p
    have hx: Sown z E ρ ε τ p₀ W := (f.away i s).tack f (by rw [Broad_turn]; exact west K i s _ hp)
    have hw:= a i z1 (buffet A) (f.occupy.mono hp)
    obtain ⟨Y,a',b,r,g'⟩:= ih W hx (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at Vv; exact Vv.trans' (le_of_eq (by ring)))
    refine ⟨Y,a',?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold W U; rw [List.length_append,List.length_map]; ring -- W/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z1) (buffet A)*buffet A=buffet W:=by unfold W U; rw [buffet_tack,buffet_turn] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma scattering (g:N=K.c m)(Vv:2^l*(B+addgap K)≤ N.val)(S:Finset Axis) (A:List (Hookah N))(f:Sown z E ρ ε τ p₀ A)
    (p:∀ a∈S,cows a (Broad p₀ A) B) : ∃ U:List (Hookah N), Sown z E ρ ε τ p₀ U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (buffet A)‖^((2^l)^S.card) ≤ ‖ν (buffet U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,a₁,b,vL⟩:= stance (ν:=ν) a g A i f (p i (mem_insert_self ..)) Vv
    obtain ⟨Z,gX,e,l'⟩:= ih U hU (fun s v=> vL s (fun h=>x (h ▸ v)) _ (p s (mem_insert_of_mem v))) -- extras
    rw [card_insert_of_notMem x,pow_succ']; refine ⟨Z,gX,?_,?_⟩
    · rw [e,a₁]; ring
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) b _).trans l'
omit a
private lemma goldilock {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
include a
lemma trifecta (g:N=K.c m)(Vv:B+addgap K≤ N.val)(A:Hookah N)(f:Vote z E ρ ε τ A)(p:∀ i,cows i (Lattice.halo p₀ A.S) B) :
    ∃ U: List (Hookah N), Sown z E ρ ε τ p₀ U ∧ 0<U.length ∧ U.length ≤ (More N).val^4 ∧
       (More N).val^4 ≤ U.length*(4*(B+addgap K))^4 ∧ ‖ν A.x‖^U.length≤ ‖ν (buffet U)‖:=by
 obtain ⟨k',a₁,l⟩:= goldilock (x:=N.val) (show 0 < B+addgap K from Nat.add_pos_right _ addgap_pos) Vv
 obtain ⟨U,f',H,hY⟩:= scattering (ν:=ν) a g a₁ univ [A] (Sown.one f) (fun i b=>by simpa [Broad_more] using p i) -- whereF
 have hw:(univ: Finset Axis).card=4:=by simp [Axis]
 have hp:U.length=(2^k')^4:= by simpa [hw] using H
 refine ⟨U,f',?_,?_,?_,?_⟩
 · rw [hp]; positivity
 · change _ ≤ (N.val*2)^4; rw [hp]; apply pow_le_pow_left'; have hq:= a₁.trans' (Nat.le_mul_of_pos_right (2^k') (Nat.add_pos_right _ (show 0 < addgap K from addgap_pos))); omega
 · rw [hp,← mul_pow]; apply pow_le_pow_left'; change N.val*2 ≤_; apply le_trans (Nat.mul_le_mul_right 2 l); exact le_of_eq (by ring)
 rw [hp]; simpa only [hw,buffet_more,buffet_empty,mul_one] using hY
omit a
end Hookah.Blaze
end YM.CF.Lamour.Bridge.Celeste.Clock
#print axioms YM.CF.Lamour.Bridge.Celeste.Clock.Hookah.Blaze.trifecta
#print axioms YM.CF.Lamour.Bridge.Celeste.Clock.Hookah.Blaze.silk_warm
