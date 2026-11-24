import YM.SU5.Relativistic.Caplets
import YM.SU5.Relativistic.Juncture
/-!
Repurpose the flag-counting from Sheds.
# Four-volume budget at density.  Distinct clean subset chosen before integrating:
Yep is a pointwise bound even with discontinuous good/dirty designation.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate (sites)
open Py.Rate.Pannier
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}{k:ℕ}

variable {c:ℕ}{γ':ℝ}{L:List (Cliplet n k)}{U:Pane n}{j w d t:ℕ}{γ τ R ε δ δ':ℝ}{M:Tulip.Male}
private lemma twoWay {α:Type*} (L:List α)(f:α→Bool)(u:α→Bool): ∃ b:Bool, (L.filter f).length ≤ 2 * (L.filter fun x=> f x && u x==b).length:=by
 let X:=L.filter f; let Y:= X.filter u; let F:= X.filter fun x=> !u x
 have he: (Y++F).Perm X:= List.filter_append_perm u X
 have hp: Y = L.filter (fun x=> f x && u x == true):=by unfold Y X; rw [List.filter_filter]; congr 1; funext x; simp [and_comm,Bool.and_comm] -- tune
 have hf: F= L.filter (fun x=> f x && u x == false):=by unfold F X; rw [List.filter_filter]; congr 1; funext x; cases u x <;> simp
 have hh:Y.length+F.length=X.length:=by simpa only [List.length_append] using he.length_eq
 rcases le_total Y.length F.length with g|g; exact ⟨false,by rw [←hf,show (L.filter f).length=X.length from rfl]; omega⟩
 exact ⟨true,by rw [←hp,show (L.filter f).length=X.length from rfl]; omega⟩
private lemma margin {D F:List (Cliplet n k)}(h:Company j M w d c t γ γ' τ ε R L)(d:D.Sublist L)(f:F.Sublist L)(u:∀ i∈D,i∉ F): Disjoint (whereV D) (whereV F):=by
 apply disjoint_left.mpr; intro x hx hy; obtain ⟨A,g,v⟩:=(whereV_at ..).1 hx; obtain ⟨B,w,hx⟩:=(whereV_at ..).1 hy; exact disjoint_left.mp (h.distinct (d.mem g) (f.mem w) (by rintro e; exact u A g (e.symm ▸ w))) v hx
private lemma prod_perm {D:List (Cliplet n k)} (h:Company j M w d c t γ γ' τ ε R L)(p:L.Perm D)(x:Fields n)(u:0<k) : probe L x=probe D x:=by
 rw [probe_at,probe_at]; apply (p.map (fun A=> A.frame x)).prod_eq'; rw [List.pairwise_map]; have he(A)(v:A∈ L):Fine (Tset n) univ false (A.frame x):= Window.fine_enlarge (subset_univ _) ((h.granted A v).atCost.allV x); exact (h.nodup u).pairwise_of_forall_ne (fun i hi j hj _=> fineWise (he i hi) (he j hj))
private lemma isDirt {t:ℕ}{u:Finset (Seat n)}{A:(Cliplet n k)}(h:¬ Disjoint (Lattice.halo t A.broad) u) :
    ∃ i∈ A.broad,i∈ Lattice.halo t u:=by obtain ⟨i,h,t'⟩:= Finset.not_disjoint_iff.mp h; obtain ⟨v,q,l⟩:= halo_spec.mp h; exact ⟨v,q,halo_spec.mpr ⟨i,t',(separation_comm ..).trans_le l⟩⟩
private lemma seekNumber {Z:Finset (Seat n)} (d' : 0<k)(h:Company j M w d c t γ γ' τ ε R L)(p:∀ a∈L, ∃ i∈ a.broad,i∈ Z) : L.length≤ Z.card:=by
 induction L generalizing Z with
 | nil=> simp
 | cons a L ih=>
    obtain ⟨x,q,g⟩:= p _ List.mem_cons_self
    have ht:L.length≤ (Z.erase x).card:=by
      apply ih (h.shorter (by simp)); intro i u; obtain ⟨y,t,v⟩:= p i (List.mem_cons_of_mem _ u); refine ⟨_,t,mem_erase.mpr ⟨fun k=> ?_,v⟩⟩; exact disjoint_left.mp ((List.pairwise_cons.mp h.lock).1 i u) q (k ▸ t) -- nested eq
    rw [Finset.card_erase_of_mem g] at ht; rw [List.length_cons]; have ho:= Finset.card_pos.mpr (show Z.Nonempty from ⟨x,g⟩); omega
private lemma orders (d':0<k)(h:Company j M w d c t γ γ' τ ε R L) (V:Pane n) :
    ∃ (W D:List (Cliplet n k))(u:Bool), W.Sublist L ∧ D.Sublist L ∧ Disjoint (whereV W) (whereV D) ∧ L.Perm (W++D) ∧
    L.length ≤ 2*W.length+ (roughness τ V).card * (4*(t+t+1)^4) ∧ ∀ a∈W,a.feel τ t V ∧ a.rev=u:=by
 classical
 let f(a:Cliplet n k):= decide (a.feel τ t V); let F:=L.filter f; let K:= L.filter (fun a=> !f a); have p : (F++K).Perm L:= List.filter_append_perm f L; obtain ⟨u,w⟩:=twoWay L f Cliplet.rev; let g(a:Cliplet n k):= f a && a.rev==u
 let W:=L.filter g; let B:= L.filter fun z=> !g z; have hf:W.Sublist L:=List.filter_sublist; have hg:B.Sublist L:=List.filter_sublist
 have ht: K.length≤ (roughness τ V).card * (4*(t+t+1)^4):=by
    apply (seekNumber (Z:=Lattice.halo t (flags τ V)) d' (h.shorter (show K.Sublist L from List.filter_sublist)) (fun i v=> isDirt ?_)).trans ((Corona.halo_size ..).trans ?_)
    -- goal order
    all_goals first
    | exact (Nat.mul_le_mul_right _ (flag_coat V τ)).trans_eq (Nat.mul_assoc ..)
    | exact (show ¬ i.feel τ t V from by have hk:= (List.mem_filter.mp v).2; simpa [f] using hk)
 have hx:L.Perm (W++B):= (List.filter_append_perm g L).symm
 refine ⟨W,B,u,hf,hg,margin h hf hg (fun i h t=> (by have hp:= (List.mem_filter.mp h).2; have hg:(!g i)=true:= (List.mem_filter.mp t).2; rw [show g i=true from hp] at hg; contradiction)),hx,?_ ,fun i he=>?_⟩
 · calc
   _ = F.length+K.length:= by simpa only [List.length_append] using p.length_eq.symm
   _ ≤ _ := Nat.add_le_add w ht
 have t: g i=true:= (List.mem_filter.mp he).2; simpa [g,f] using t

private def fir (L:List (Cliplet n k)):List (berries L):= L.attach ×ˢ (List.ofFn id)
private lemma packsProd (f:berries L→FC (Single n)) (X:Fields n)(p:∀ i:Actor L,i.val.frame X=xpert fun a=> f (i,a)): probe L X=( (fir L).map f).prod:=by
 rw [probe_at]; generalize hx: L.attach =W at * -- affects fir
 rw [show fir L=W ×ˢ List.ofFn (@id (Fin k)) from ?_]; swap; · unfold fir; rw [hx] -- both lists
 have ht:W.map Subtype.val=L:= hx ▸ List.attach_map_subtype_val _
 conv_lhs=>arg 1; rhs; rw [←ht] -- unfold check; easier rewrite occ using calc
 rw [List.map_map]; clear hx ht
 induction W with
 | nil=> rfl
 | cons a L ih=> rw [List.product_cons,List.map_append,List.prod_append, List.map_cons, List.prod_cons,ih,List.map_map,List.map_ofFn]; exact congrArg (· * _) (p a)


abbrev meridiem (R:ℝ):= (2+R)^5
lemma Company.bill (h:Company j M w d c t γ γ' τ ε R L) (p:0≤R)(x:Fields n): ‖probe L x‖≤ (1+meridiem R)^(L.length*k):=by
 let q:= 1+meridiem R; have hp:0≤q:=by unfold q meridiem; positivity
 change _≤ q^_
 induction L with
 | nil=> simp
 | cons i L ih=>
   rw [probe_cons,Pi.mul_apply]; obtain ⟨V,X,Z,_,q',_,_,u,_,t',_⟩:= (h.granted i List.mem_cons_self).peak x; rw [q']
   let F(a:Fin k)(c:Ring5):= handy i.rev (Tset n) (X a c) (Z a c); let A:= fun a=> prime (F a); have he(a):‖A a‖ ≤q:= by apply le_trans (liquidate (F a) (1+R) (by linarith) (fun i=>Perron.peakCost _ _ (u a i) (t' a i))); apply le_of_eq; unfold q meridiem; rw [show (1+(1+R))=2+R by ring]
   have hs: ‖xpert A‖≤ q^k:=by
     let K:= List.ofFn (@id (Fin k)); have ht:xpert A= (K.map A).prod:=by rw [show K.map A=_ from List.map_ofFn]; rfl
     rw [ht]; exact (quantity_list A q hp K (fun i _=> he i)).trans_eq (by rw [show K.length=k from List.length_ofFn])
   rw [List.length_cons,add_comm L.length, Nat.add_mul,one_mul,pow_add]
   exact (norm_mul_le ..).trans (mul_le_mul hs (ih (h.shorter (by simp))) (norm_nonneg _) (pow_nonneg hp _))

private lemma aperture (x U Y k:ℕ)(Z F T:ℝ) (h:(x:ℝ)≤2*(U:ℝ)+Y)(u:0≤Z)(v:0≤F)(g:0≤T)(t:F≤ Real.exp (-2*(Z+T))) :
    F^(U*k)*(1+T)^(x*k) ≤ Real.exp (-(Z*(x*k:ℕ))+(Z+T)*(Y*k:ℕ)):=by
 have hg: 1+T≤ Real.exp T:=by linarith [Real.add_one_le_exp T]
 apply (mul_le_mul (pow_le_pow_left₀ v t (U*k)) (pow_le_pow_left₀ (show 0 ≤ 1+T by linarith) hg (x*k)) (by positivity) (by positivity)).trans; rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]; apply Real.exp_le_exp_of_le; push_cast
 have he:0≤Z+T:=by linarith
 nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α:=ℝ) k)) he]

open Damask
private lemma enlist {W:List (Cliplet n k)}{X₁ Y Y':(berries W)×Ring5→Ket (Single n)}{P:Op (Single n)}{d':Bool}{Φ Θ:Wave (Single n)}{T:Finset (Seat n)}{G':FC (Single n)}[DecidableEq (berries W)] [DecidableEq (berries W × Ring5)] (p:0<R)(e:ℝ)(r:0<e)(r':e ≤ 1)
    (hP:IsStarProjection P)(b:Sea P Φ)(b':Sea (cutM (Tset n)) Θ) (uX:∀ i,trim (hand (!d') (cutM (Tset n))) (X₁ i))
    (vX:∀ i,‖X₁ i‖ ≤ 1)(qF:∀ i,trim (hand d' P) (Y i))(hF:∀ i,‖Y i‖ ≤ R+e^3)(u₀:∀ i,withinM (modesIn n T)ᶜ (Y' i))(q₀:∀ i,‖Y' i-Y i‖ ≤ e^3)
    (hY:∀ i l, inner ℂ (X₁ i) (Y l) = if i=l then 1 else 0)(ht':∀ i l,inner ℂ (X₁ i) (Y' l) = if i=l then 1 else 0)(h₁:∀ i,‖Y' i‖≤ R)
    (hG: Fine (Tset n) (modesIn n T) false G') (v:Fields n) (hx:∀ a:Actor W,a.val.frame v=xpert (fun j=>prime (fun c=>handy d' (Tset n) (X₁ ((a,j),c)) (Y' ((a,j),c))))) (hp:W.Nodup):
      Yep e⁻¹ (acts (star (probe W v*G')) Θ) Φ ((5*(e*(R+4)*meridiem R))^(W.length*k)*‖G'‖):=by
    classical
    let H:= fir W; let F₀:=5*(e*(R+4)*meridiem R); let Z₁(i:Cliplet.berries W):= prime (fun c=> handy d' (Tset n) (X₁ (i,c)) (Y' (i,c)))
    change Yep _ _ _ (F₀^_*‖G'‖)
    have hk:H.length=W.length*k:=by unfold H fir; rw [List.length_product]; simp
    have hx':probe W v=fo Z₁ H:=packsProd Z₁ v hx
    rw [hx',←hk]; apply (Pledge.gives (A:=fun i c=> X₁ (i,c)) (Y':=fun i c=>Y (i,c)) (Z':=fun i c=> Y' (i,c)) (b:=d') hP b b' r r' (show 0<R+4-3 by linarith) (show 1 ≤ 2+R by linarith) (fun i c=> uX _) (fun i c=> vX _) (fun i c=> qF _) (fun i c=> q₀ _) ?_ ?_ ?_ ?_ G' (Window.fine_enlarge (subset_univ _) hG) (fun i j=> comm_lost hG.sector (u₀ _)) H (hp.attach.product (List.nodup_ofFn_ofInjective injective_id))).weigh ?_ (by positivity)
    · intro i j; apply (hF (i,j)).trans; have he: e^3 ≤ 1:= pow_le_one₀ r.le r'; linarith
    · intro i c j h; change inner ℂ (Y (i,c)) (X₁ (j,h))=_; rw [←inner_conj_symm,hY]; by_cases w:(i,c)=(j,h); · have e:i=j ∧ c=h:= Prod.mk.inj w; rcases e with ⟨rfl,rfl⟩; simp
      by_cases u:i=j ∧ c=h; · obtain ⟨rfl,rfl⟩:=u; exact (w rfl).elim
      rw [if_neg u,if_neg (Ne.symm w)]; simp -- tune ordering
    · intro i j l k h; rw [←inner_conj_symm,ht',if_neg ?_]; simp; intro k; exact h.elim (fun x=>x (Prod.mk.inj k.symm).1) (fun x=>x (Prod.mk.inj k.symm).2)
    · intro i j; exact (norm_sub_le ..).trans ((add_le_add (show ‖(1:FC (Single n))‖ ≤ 1 by simp) (Perron.peakCost _ _ (vX (i,j)) (h₁ _))).trans_eq (by ring))
    exact le_of_eq (by unfold F₀ meridiem; ring)

set_option maxHeartbeats 250000 in
lemma density {A0:Orbit n→ Pane n}(h:Company j M w d c t γ γ' τ ε R L)(p:0<R)
    (u:ℝ)(l:ℕ)(P:Roof n u δ' l A0)(s:τ≤u)(q:l+c ≤ t)
    (S:Sparkle n δ' M j)(v:0≤δ)(y:δ'≤δ)
    {κ ε' C:ℝ}(A:Winter j δ n γ w κ)(A':Winter j δ n γ' c ε')(U:∀ (i:Finset (Seat n)),Sparse d i→∀ b,HearthB C (sp b j M (1:Pane n)) i)(x:κ*C≤1/3)
    (e:ℝ)(r:0<e)(r':e ≤ 1)(g:(ε'*R+ε)+2*C*(ε'*R+ε) ≤ e^3)
    (Z D η:ℝ)(hp:5*(e*(R+4)*meridiem R)≤Real.exp (-2*(Z+meridiem R)))(ht:0≤Z)(z:Z*η≥ D) (pL:(L.length*k:ℕ)≥ η*sites n)(k':0<k)
    (X:Orbit n)(Φ Θ:Wave (Single n))(b:Sea (spar j M (A0 X)) Φ)(b':Sea (cutM (Tset n)) Θ) : Yep e⁻¹ (acts (star (probe L (X.1,A0 X))) Θ) Φ (Real.exp (-(D*sites n) + ((Z+meridiem R)*(4*(t+t+1)^4*k:ℕ))*flakes τ X.1)):=by
 classical
 obtain ⟨W,G,d',u',kG,tWG,kL,v₀,F⟩:= orders k' h X.1; let f:Fields n := (X.1,A0 X); let P':= h.shorter u'; let Q:= h.shorter kG; let G':= probe G f
 have hu(i)(p:i∈W):i.rev=d' ∧ i.feel τ t f.1 ∧ Agrees (hot i c) f.2 f.1:=by
    obtain ⟨ht,hp⟩:= F i p; refine ⟨hp,ht,Py.Rate.Pannier.fledged P (hot i c) X s ?_⟩; apply Finset.disjoint_left.mpr; intro x ht' v; obtain ⟨y,w,h₀⟩:=halo_spec.mp ht'; obtain ⟨j,u,g⟩:=halo_spec.mp w; exact disjoint_left.mp ht (halo_spec.mpr ⟨j,u,(separation_triangle j y x).trans (by omega)⟩) v
 obtain ⟨X₁,Y,Y',uX,vX,qF,hF,u₀,q₀,hY,ht',h₁,h₂⟩:= assemblage (v:=f) P' S A v (P.paid X) y A' (fun i g=> U i g d') x g hu (whereV G) tWG.symm
 let F₀:=5*(e*(R+4)*meridiem R); let Z₁(i: Cliplet.berries W):=prime (fun c=>handy d' (Tset n) (X₁ (i,c)) (Y' (i,c))); let V:= 1+meridiem R; have hT:0≤ meridiem R:=by unfold meridiem; positivity
 let C':= Z+meridiem R; let H:= fir W; have hk:H.length=W.length*k:=by unfold H fir; rw [List.length_product]; simp
 have hG: Fine (Tset n) (modesIn n (whereV G)) false G':= Q.corsage.allV f
 have He: Yep e⁻¹ (acts (star (probe L f)) Θ) Φ (F₀^(W.length*k)*‖G'‖):=by
    rw [prod_perm h kL f k',probe_combine,Pi.mul_apply]
    exact enlist p e r r' (S.projection _ (P.paid X)) b b' uX vX qF hF u₀ q₀ hY ht' h₁ hG f h₂ (P'.nodup k')

 have hR:0≤F₀:=by unfold F₀; positivity
 apply He.weigh (le_trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hR _)) ((aperture L.length W.length ((roughness τ X.1).card * (4*(t+t+1)^4)) k Z F₀ (meridiem R) (by exact_mod_cast v₀) ht hR hT hp).trans (Real.exp_le_exp_of_le ?_))) (by positivity)
 · exact (Q.bill p.le f).trans (pow_le_pow_right₀ (by linarith only [hT]) (Nat.mul_le_mul_right _ kG.length_le))
 unfold flakes; have he:= mul_le_mul_of_nonneg_left pL ht; push_cast; push_cast at he; nlinarith only [he,mul_le_mul_of_nonneg_right z (show 0≤ sites n by unfold sites; positivity)]
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.density
