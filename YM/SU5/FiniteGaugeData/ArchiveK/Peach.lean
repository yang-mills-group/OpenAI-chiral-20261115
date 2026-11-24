import YM.SU5.FiniteGaugeData.ArchiveK.Gene
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
namespace Midway
open Violas LightK Concert Waltz Ledger
variable {n N κ ℓ D c i d k:ℕ}{r K σ C ε:ℝ}{G:E4≃ₗᵢ[ℝ] E4}(P:ZephyrG G D c) (L:FilterK)
lemma ap_box (S:Side) (t:2*n<S.val): Waltz S (box n) := by
 intro i p x h a; have he:= box_test.mp (show i∈box n from p); have hb:=box_test.mp (show x∈box n from h); funext z;
 apply wrap_d _ _ (congr_fun a z); have hu:= he.1 z; have hx:= he.2 z; have hh:= hb.1 z; have hl:= hb.2 z; omega
-- for any b use. iteration scale 
local notation "Ω"=> box n
structure Dossier (S' A B:Finset Cover) (m n:ℕ)(ε:ℝ):Prop where
 run : ∃ a b:ℕ,∀ (N:Side)(M:Tulip.Male), a ≤ N.val→ b≤ M.val.val → Suite m N M S' A B (perF 16384 n) (perF 16384 n) (perF (-ε) n)
variable (Z:0<σ) (v:0<r)(h:r≤1)(p:0≤ K)(w:∀ x:Cover,‖fpS x‖≤K)(H:∀ M:Tulip.Male,Ream (bar 4 M.val) σ C)
variable (b:Bool) (A: Ledger P L (64*i) n (perF (-4096) n) r)
local notation "U₀"=> Lft L P b A -- order? look in Exhibit L K.
local notation "V₀"=> Rht L P b A
include Z v h p w H
lemma shipC (e:Lft L P b A⊆ box n)(g:Rht L P b A⊆ box n) (x:∀ x∉box n,∀ v∈Rht L P b A,River r (emitX x) (emitX v)) (u:lien G L K σ C ε r i d n k): Dossier (box n) U₀ V₀ (i*n^3) n ε:= by
 let T:= box (n+d*n); have ht: Ω ⊆ T:=fun a j=>box_test.mpr (let z:=box_test.mp j; ⟨fun i=> by have a:=z.1 i; omega, fun i=>by have b:=z.2 i; omega⟩); have hw:∀ x∈ Ω,∀ v∈box (d*n), x-v∈T:=by
    intro i z v t; obtain ⟨l,w⟩:= box_test.mp z; obtain ⟨x,p⟩:=box_test.mp t; refine box_test.mpr ⟨fun i'=>?_,fun i'=>?_⟩; specialize l i'; specialize p i'; rw [Pi.sub_apply]; omega; specialize w i'; specialize x i'; rw [Pi.sub_apply]; omega
 let X:= U₀; let Y:= V₀; let W:= i*n^3; let U:= perF 8192 n; have hx:0<U:=Real.exp_pos _; let η:=stake K (page (Beam Y)) (page (Beam T)) (i*n^3) U; let Z':= inertial K r σ C (page (Beam Y)) (page (Beam T)) (i*n^3) (d*n) k U; obtain ⟨uκ,G,uα⟩:= u; obtain ⟨h₀,U',T₀⟩:= uα (page (Beam X)) (page (Beam Y)) (page (Beam T)) (volumeP_m e) (volumeP_m g) le_rfl; -- rename v
 have he:found (Pick X Y) (2*W) U⁻¹:= by
    unfold U; rw [show (perF 8192 n)⁻¹= perF (-8192) n from (by unfold perF; rw [neg_mul,Real.exp_neg])]; apply Ledger.«use» L P b A (2*W) k G (Real.exp_pos _) h₀
 obtain ⟨B,hB⟩:= messageR X Y e g ht hw Z v h x K w p H hx uκ he
 refine ⟨2*(n+d*n)+1,B,fun N M t₀ s=>?_⟩; obtain ⟨V,P,Q,Y',hQ⟩:= (hB M s N (ap_box N t₀)).choice; exact ⟨V,P,Q,Y'.bill' U' U' T₀,hQ⟩
-- tune cap extraction placeholders
omit Z v h p w H
structure Demand (ℓ n m:ℕ)(ε:ℝ)(A B A' B':Finset Cover):Prop where
 hull(b:Bool): (if b then A else A')⊆ box n ∧ (if b then B else B')⊆ box n
 lanes(b:Bool): Land b ℓ (if b then A else A') ∧ Land (!b) ℓ (if b then B else B')
 mark(b:Bool): Disjoint (if b then A else A') (if b then B' else B)
 scales(b:Bool): (if b then A else A').card≤64*m
 bill(b:Bool): Dossier (box n) (if b then A else A') (if b then B else B') m n ε
-- tune lanes Bool.False run AP. view uses Apos when b.Etc.
#print axioms shipC
variable (s:0≤ C)
include s H Z
lemma accessK (i ℓ:ℕ) (z:0 < i)(t:0≤ε) : ∃ᶠ n:ℕ in atTop, ∃ A B A' B':Finset Cover,Demand ℓ n (i*n^3) ε A B A' B':= by
 obtain ⟨u,s',p,t0⟩ : ∃ u:ℕ,0<u∧TokenF ε≤σ*u∧True:=by
    obtain ⟨u,b⟩:= exists_nat_gt (TokenF ε/σ); refine ⟨u,Nat.cast_pos.mp (lt_trans ?_ b),((div_lt_iff₀ Z).1 b).le.trans_eq (mul_comm ..),trivial⟩; exact div_pos (by unfold TokenF; positivity) Z
 obtain ⟨B,b,v⟩:= Midway.squares i z; -- Qloss and pub
 let T:=TokenF ε; let α:= Real.exp (-T*B); have hu:0 < α:=Real.exp_pos _; have he:α≤ 1:= Real.exp_le_one_iff.mpr (by unfold T TokenF; rw [neg_mul,neg_nonpos]; positivity); obtain ⟨X⟩:= taxi (64*i) hu; obtain ⟨V,h₁,hV⟩:= X.cap_l
 obtain ⟨a,b0⟩:=exists_nat_gt (4*V); obtain ⟨G,D,t',K⟩:= unusual a 0; obtain ⟨L,c⟩:= LightK.pearl (r:=V) K b0.le; let L':= X.knot D B; have hx:= X.knotT b t'
 obtain ⟨K',g,G'⟩:= axiom_bud_fp; apply hx.frequently ?_; -- tune convert frequently. Filter.Tendsto.frequently etc
 let f:= res L K X b hu he V (fun x=> hV D t' x) c; let T':= hx.eventually (earning L G K' σ C ε t Z s g.le u i p);
 apply Filter.Eventually.frequently; filter_upwards [((eventually_all (ι:=Bool)).mpr f), T', hx.eventually_gt_atTop 0,eventually_all.mpr (fun i:Genre (64*_)=> (RayT X b t' i).eventually_ge_atTop (ℓ:ℝ))] with n h TTT Hn φ
 let N:= L' n; choose U W using h; let A(c):=Lft L K c (U c); let B'(c):=Rht L K c (U c); let m:=i*N^3; have ht:N>0:=Hn; let j:=X.divKH D B n; have hl:j * B=N:= X.knot_div b t' n; have hg:0<j:=Nat.pos_of_ne_zero (fun e=>by rw [←hl,e,zero_mul] at ht; omega)
 obtain ⟨b₀,v₀⟩:=v j hg; -- reduce casts at hl from let x variable order.j.n
 have hp:lien G L K' σ C ε α i u N j:=by
    have hs:α^j=perF (-TokenF ε) N:=by unfold perF α; rw [←Real.exp_nat_mul,←hl]; push_cast; unfold T; ring_nf -- T shadow T_tickets.
    obtain Dp:= TTT j α hs.le; -- tune
    rw [hl] at b₀ v₀; exact ⟨b₀,v₀,fun a b t h p e=> Dp t b a p h e⟩
 let P(c):=Twig.estate L K X b hu he (U c) (W c); let V'(c):=Twig.Lanes L K X b hu he (U c) (W c) ℓ φ
 have hea(c:Bool) : Dossier (box N) (A c) (B' c) m N ε:= shipC K L Z hu he g.le G' H c (U c) (P c).1 (P c).2.1 (P c).2.2 hp -- tune argument
 show ∃ A B A' B':Finset Cover,Demand ℓ N m ε A B A' B'; refine ⟨A true,B' true,A false,B' false,fun bX=> ?_,fun bX=>?_,fun b'=>?_,fun c=>?_,fun bX=>?_⟩
 · cases bX <;> exact ⟨(P _).1,(P _).2.1⟩ -- tune implicit bool metavars.
 · cases bX; exact V' false; exact V' true
 · cases b'; exact Twigs_apart L K X b hu he _ (W false) (W true); exact Twigs_apart L K X b hu he _ (W true) (W false)
 · have hx:64*i*N^3=64*m:=by unfold m; ring;
   cases c<;> simp only [Bool.false_eq_true,↓reduceIte]; exact (Twig.bank L K X b hu he _ (W false)).trans_eq hx; exact (Twig.bank L K X b hu he _ (W true)).trans_eq hx
 cases bX; exact hea false; exact hea true
#print axioms accessK
end Midway
end YM.CF.Window.ArchiveK
