import YM.SU5.Relativistic.Pincer
/-! # Aperture charges for tilted stencil. Need neighborhoods after paid Θ epsilon. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier.Chancel Buffered
open Crest.Sleet
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
-- star by recursion via word grammar
inductive Staff where | pay | gauge | one | add : Staff→Staff→Staff| neg:Staff→Staff| mul:Staff→Staff→Staff
namespace Staff
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I]
variable (B P:Op I)
def stem (s:Staff)(B P:Op I): Op I:=match s with
 | pay=>P
 | gauge=>B
 | one=>1
 | add a b=> a.stem B P+b.stem B P
 | neg a=> -(a.stem B P)
 | mul a b=> a.stem B P*b.stem B P
def ice :ℕ→ Staff|0=>add one (neg one)|n+1=> let V:=pay; add (mul (mul (add one (neg V)) gauge) V) (mul (ice n) (add one (neg (mul (mul pay gauge) pay))))
lemma ice_at(n:ℕ) : (ice n).stem B P=Comb B P n :=by induction n with| zero=> simp [Comb,ice,stem]|succ n ih=> rw [ice, Comb]; simp only [stem]; rw [ih]; abel -- tune sub
lemma power(s:Staff) : ∃ C> (0:ℝ),∀ (N:Side),∀ (X:Op (Single N)) (h:IsStarProjection X), ‖s.stem (tickA N) X‖ ≤ C:=by
 induction s with
 | one=> exact ⟨1,zero_lt_one,fun _ _ _=> norm_one.le⟩
 | gauge=>exact ⟨1,zero_lt_one,fun n P _=> (show IsStarProjection (tickA n) from (by rw [←t_comp]; exact cutM_idp _)).norm_le _⟩
 | pay=> exact ⟨1,zero_lt_one,fun n _ h=> h.norm_le _⟩
 | add a b ih ih'=> obtain ⟨P,p,h⟩:=ih; obtain ⟨Q,q,h'⟩:=ih'; exact ⟨P+Q,add_pos p q,fun n X t=>(norm_add_le ..).trans (add_le_add (h n X t) (h' n X t))⟩
 | neg a ih=> obtain ⟨P,p,h⟩:=ih; exact ⟨P,p,fun n X t=> (norm_neg _).trans_le (h n X t)⟩
 | mul a b ih ih'=> obtain ⟨P,p,h⟩:=ih; obtain ⟨Q,q,h'⟩:=ih'; exact ⟨P*Q,mul_pos p q,fun n X t=>(norm_mul_le ..).trans (mul_le_mul (h n X t) (h' n X t) (norm_nonneg _) p.le)⟩
def flip:Staff→ Staff| add a b=> add a.flip b.flip| mul a b=> mul b.flip a.flip| neg a=> neg a.flip| t=>t
lemma flip_p (s:Staff)(p:IsStarProjection P)(b:IsStarProjection B): s.flip.stem B P=star (s.stem B P):=by induction s <;> simp_all only [stem, flip, star_mul,star_one,star_add, star_neg] <;> first|exact p.isSelfAdjoint.star_eq.symm| exact b.isSelfAdjoint.star_eq.symm
lemma spin(p:Staff)(B Q:Op I)(U:UNI I): twist U (p.stem B Q)= p.stem (twist U B) (twist U Q):=by induction p <;> simp_all only [stem,map_one,map_neg,map_mul,map_add]
variable {N:Side}{δ r γ u ε:ℝ}{j v T K:ℕ}
private lemma shath (i:ℕ) (S:Finset (Seat N)) : S⊆ Lattice.halo i S:=by intro x v; exact halo_spec.mpr ⟨x,v,(by simp)⟩
lemma crease {S S':Support (More N)}(h:T ≤ K)(hh:S⊆ S') : Lattice.halo T S⊆ Lattice.halo K S':=by intro x v; obtain ⟨y,g,e⟩:=halo_spec.mp v; exact halo_spec.mpr ⟨y,hh g,e.trans h⟩
lemma hollowG {T Q:ℕ}(S: Finset (Seat N)) : Lattice.halo T (Lattice.halo Q S)⊆ Lattice.halo (Q+T) S:=by intro x v; obtain ⟨y,h,g⟩:= halo_spec.mp v; obtain ⟨z,b,t⟩:=halo_spec.mp h; exact halo_spec.mpr ⟨z,b,(separation_triangle z y x).trans (Nat.add_le_add t g)⟩
lemma rightfulInv {U V:Pane N}{F T:Support (More N)}(h:Rightful F U V u)(p:T⊆ F)(g:u ≤ r): Rightful T U V r:=fun i hi=> (h i (mem_filter.mpr ⟨(mem_filter.mp hi).1,p (mem_filter.mp hi).2.1,p (mem_filter.mp hi).2.2⟩)).trans g -- implicit
lemma cut_snap{a b: Support (More N)}(h:a⊆b)(P:Op (Single N)): ‖Vo a*P‖≤ ‖Vo b*P‖:=by
 have he:Vo a*Vo b=Vo a:=cut_from_left _ _ (modes_monotone h); nth_rw 1 [←he]; rw [mul_assoc]; exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _))
variable (M:Tulip.Male)(j:ℕ)(δ:ℝ)
def Stage (s:Staff)(j N:ℕ)(δ:ℝ)(L:ℕ)(γ ε:ℝ):Prop:=∀ {n:Side}, N ≤ n.val→∀ (M:Tulip.Male),∀ G:Support (More n), let U:=spar j M (1: Pane n); let F:=tickA n;let X:=s.stem F U; IsStarProjection U → ‖Vo (Lattice.halo L G)ᶜ*(X *Vo G)‖≤ε ∧∀ (P:Pane n), Guard P δ→ Rightful (Lattice.halo L G) P 1 γ → IsStarProjection (spar j M P) →‖(s.stem F (spar j M P)-X)*Vo G‖≤ε
lemma stage_big (s:Staff) (p:s.Stage j v δ K γ ε)(h: T≥K)(t:u ≤γ)(g:ε≤r): s.Stage j v δ T u r:=by
 intro n d m F U f X x; obtain ⟨u,hp⟩:=p d m F x; let S:=Lattice.halo T F; have hh:Lattice.halo K F⊆ S:=crease h (subset_refl _); exact ⟨((cut_snap (compl_subset_compl.mpr hh) _).trans u).trans g, fun P hx ex w=>(hp P hx (rightfulInv ex hh t) w).trans g⟩
variable (z:0≤δ)(W:∀ e>(0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,v≤ n.val→Winter j δ n γ w e)
include z W
lemma playsA(s:Staff): ∀ ε> (0:ℝ),∃ γ> (0:ℝ),∃ L:ℕ, s.Stage j v δ L γ ε:=by
 induction s with
 | one=>
   intro ε e; refine ⟨1,zero_lt_one,0,?_⟩; intro n p m F U A X h; constructor; · change ‖Vo _*((1:Op _)*_)‖≤_; rw [one_mul,Vo_neg,sub_mul,one_mul,show Vo _ * Vo F=Vo F from cut_from_right _ _ (modes_monotone (shath 0 F)),sub_self,norm_zero]; exact e.le -- tune
   intro R h t x; unfold X Staff.stem; rw [sub_self,zero_mul,norm_zero]; exact e.le
 | gauge=>
   intro ε e; refine ⟨1,zero_lt_one,0,?_⟩; intro n p m F U A X h; constructor; · change ‖Vo _*(tickA n*_)‖≤_; rw [show tickA n*Vo F= Vo F*tickA n from (by rw [←t_comp]; unfold tenureP Vo cutM; rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; congr 1; ext; rw [mul_comm]),←mul_assoc,Vo_neg,sub_mul _ _ (Vo F),one_mul,show Vo _*Vo F= Vo F from cut_from_right _ _ (modes_monotone (shath 0 F)),sub_self,zero_mul,norm_zero]; exact e.le
   intro R h t x; unfold X Staff.stem; rw [sub_self,zero_mul,norm_zero]; exact e.le
 | pay=>
   intro ε e; obtain ⟨γ,t,u,h⟩:= W ε e; refine ⟨γ,t,u,?_⟩; intro n a m S U A X p
   constructor
   · rw [←mul_assoc]; apply hearthB_cross (h n a) false m (guard0 z)
     intro i k j h; by_contra! f; exact mem_compl.mp k (halo_spec.mpr ⟨_,h,(separation_comm ..).trans_le f.le⟩)
   intro V r t' g; exact hearthB_wind (b:=false) (h n a) z r t'
 | neg s ih=>
   intro ε e; obtain ⟨γ,t,u,h⟩:= ih ε e; refine ⟨γ,t,u,?_⟩; intro n a m S U A X p
   obtain ⟨g,f⟩:= h a m S p; constructor; · unfold X Staff.stem; rw [neg_mul,mul_neg,norm_neg]; exact g
   intro V r t' z; unfold X Staff.stem; rw [show -(s.stem A (spar j m V)) - -(s.stem A U)= -(s.stem A (spar j m V)-s.stem A U) by abel,neg_mul,norm_neg]; exact f V r t' z
 | add a b ih ih'=>
   intro ε e; obtain ⟨γ,h,t,v'⟩:= ih (ε/2) (half_pos e); obtain ⟨D,k,p,w⟩:= ih' (ε/2) (half_pos e); let S:=max t p; refine ⟨_,lt_min h k,S,?_⟩; intro n d m F U B X Y; obtain ⟨vT,g⟩:=stage_big j δ a v' (le_max_left t p) (min_le_left _ D) le_rfl d m F Y; obtain ⟨h',q⟩:= stage_big j δ b w (le_max_right t p) (min_le_right γ D) le_rfl d m F Y
   constructor; · unfold X Staff.stem; rw [add_mul,mul_add]; exact (norm_add_le ..).trans (((add_le_add vT h').trans_eq (add_halves _)))
   intro P g' fT u; unfold X Staff.stem; rw [show (a.stem B _+ b.stem B _) -(a.stem B U+b.stem B U)= a.stem B (spar j m P)-a.stem B U+(b.stem B (spar j m P)-b.stem B U) by abel,add_mul]; exact (norm_add_le ..).trans ((add_le_add (g P g' fT u) (q P g' fT u)).trans_eq (add_halves _))
 | mul a b ih ih'=>
   obtain ⟨D,hD,Z⟩:= power a; obtain ⟨R,hR,X⟩:=power b
   intro ε e; let r:=ε/(4*D+4*R+4); have t:0<r:=by unfold r; positivity
   have hh:r*(4*D+4*R+4)=ε:=div_mul_cancel₀ _ (by positivity)
   obtain ⟨γ,h,k,v'⟩:= ih r t; obtain ⟨u,f,l,w⟩:= ih' r t
   refine ⟨_,lt_min h f,l+k,?_⟩; intro n d m F U B X0 p
   let S:= Lattice.halo l F; let T:=Lattice.halo k S; let W:=Lattice.halo (l+k) F
   have hp:= hollowG (T:=k) (Q:=l) F; obtain ⟨hs,g⟩:=v' d m S p; obtain ⟨hr,j'⟩:= w d m F p
   let Y:=a.stem B U; let L:=b.stem B U; let Q:=Vo S; let N':=Vo Sᶜ; let A:= Vo Tᶜ; let V:=Vo Wᶜ; let C:=Vo F
   have hx:Q+N'=1:=by unfold Q N'; rw [Vo_neg]; abel
   have hl:Y*L*C=Y*Q*(L*C)+Y*(N'*(L*C)):=by rw [show Y*(N'*(L*C)) = Y*N' * (L*C) from (mul_assoc ..).symm,←add_mul, ←mul_add,hx,mul_one,mul_assoc]
   have hw: ‖L*C‖≤R:=(norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans (X n U p))
   constructor; · apply (cut_snap (compl_subset_compl.mpr hp) _).trans; change ‖A*(Y*L*C)‖ ≤ ε; rw [hl,mul_add,←mul_assoc A]; apply (norm_add_le ..).trans
                  have he:‖A*Y‖≤D:=(norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _)).trans (Z n U p)); apply (add_le_add ( (norm_mul_le ..).trans (mul_le_mul hs hw (norm_nonneg _) t.le)) (le_trans ?_ (mul_le_mul he hr (norm_nonneg _) hD.le))).trans _; rw [←mul_assoc A]; exact norm_mul_le ..; nlinarith
   intro P τ v g'; let P':= spar j m P; let H:=a.stem B P'; let Y':=b.stem B P'
   have hs:=g P τ (rightfulInv v hp (min_le_left ..)) g'; have hg:=j' P τ (rightfulInv v (crease (Nat.le_add_right l k) (subset_refl _)) (min_le_right ..)) g'; have hy:‖H-Y‖≤D+D:=(norm_sub_le ..).trans (add_le_add (Z n P' g') (Z n U p))
   change ‖(H*Y'-Y*L)*C‖≤_; rw [show (H*Y'-Y*L)*C=H*((Y'-L)*C)+(H-Y)*Q*(L*C)+(H-Y)*(N'*(L*C)) from ?_]; swap; · rw [add_assoc, ←mul_assoc (H-Y),←mul_assoc, ←add_mul, ←mul_add,hx,mul_one]; noncomm_ring -- tune
   apply (norm_add_le ..).trans (le_trans (add_le_add_left (norm_add_le ..) _) _); apply (add_le_add (add_le_add ((norm_mul_le ..).trans (mul_le_mul (Z n P' g') hg (norm_nonneg _) hD.le)) ((norm_mul_le ..).trans (mul_le_mul hs hw (norm_nonneg _) t.le))) ((norm_mul_le ..).trans (mul_le_mul hy hr (norm_nonneg _) (by linarith)))).trans _; nlinarith
end Staff
end YM.CF.Papyrus.Franc
