import YM.SU5.Relativistic.Serifs
import YM.SU5.Relativistic.Pink
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
open Papyrus.Granat
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


private lemma JumpCost_ofFn {P:ℕ}{N:Type*}[LinearOrder N][Fintype N]{Z:ℕ}(v:Fin P→FC N)(g:∀ i,JumpCost Z (v i)) : JumpCost (Z*P) (List.ofFn v).prod:=by
 let L:= List.ofFn (@id (Fin P)); have he:=JumpCost.roll g L; unfold L fo at he; rw [List.length_ofFn,List.map_ofFn] at he; exact he
private lemma Company.costL (h:Company j M w d c t γ γ' τ ε R L) (x:Fields n): JumpCost (12*(L.length*k)) (probe L x):=by
 induction L with
 | nil=> simp; exact JumpCost.one
 | cons i L ih=>
   rw [probe_cons,Pi.mul_apply]; obtain ⟨V,X,Z,_,q',-,_⟩:= (h.granted i List.mem_cons_self).peak x; rw [q']
   let F(a:Fin k)(c:Ring5):= handy i.rev (Tset n) (X a c) (Z a c); let A:= fun a=> prime (F a); have he(a):JumpCost 12 (A a):=by
      apply costComple; apply JumpCost.low (k:=2*5) _ (by decide)
      exact JumpCost_ofFn _ (fun k=>costComple _ ((JumpCost.one.low (Nat.zero_le 2)).add ((JumpCost.letter (A:=creed (!i.rev) (X a k)) ⟨_,_,rfl⟩).mul (JumpCost.letter ⟨_,_,rfl⟩))))
   have hv:JumpCost (12*k) (xpert A):= JumpCost_ofFn _ he
   apply (hv.mul (ih (h.shorter (by simp)))).low; rw [List.length_cons]; apply le_of_eq; ring
open Damask
private lemma enlist {W:List (Cliplet n k)}{X₁ Y Y':(berries W)×Ring5→Ket (Single n)}{P:Op (Single n)}{d':Bool}{Φ Θ:Wave (Single n)}{T:Finset (Seat n)}{G':FC (Single n)}[DecidableEq (berries W)] [DecidableEq (berries W × Ring5)] (p:0<R)(e:ℝ)(r:0<e)(r':e ≤ 1)
    (hP:IsStarProjection P)(b:Sea P Φ)(b':Sea (cutM (Tset n)) Θ) (uX:∀ i,trim (hand (!d') (cutM (Tset n))) (X₁ i))
    (vX:∀ i,‖X₁ i‖ ≤ 1)(qF:∀ i,trim (hand d' P) (Y i))(hF:∀ i,‖Y i‖ ≤ R+e^3)(u₀:∀ i,withinM (modesIn n T)ᶜ (Y' i))(q₀:∀ i,‖Y' i-Y i‖ ≤ e^3)
    (hY:∀ i l, inner ℂ (X₁ i) (Y l) = if i=l then 1 else 0)(ht':∀ i l,inner ℂ (X₁ i) (Y' l) = if i=l then 1 else 0)(h₁:∀ i,‖Y' i‖≤ R)
    (hG: Fine (Tset n) (modesIn n T) false G') (v:Fields n) (hx:∀ a:Actor W,a.val.frame v=xpert (fun j=>prime (fun c=>handy d' (Tset n) (X₁ ((a,j),c)) (Y' ((a,j),c))))) (hp:W.Nodup){η:ℝ}{l':ℕ}(h:JumpCost l' G')(hη:0<η ∧ η≤1):
      Yep (η⁻¹*e⁻¹) (acts (star (probe W v*G')) Θ) Φ (Real.exp (crater (cutM (Tset n)) P η)*η⁻¹^(12*(W.length*k)+l')*(5*(e*(R+4)*meridiem R))^(W.length*k)*‖G'‖):=by
    classical
    let H:= fir W; let F₀:=5*(e*(R+4)*meridiem R); let Z₁(i:Cliplet.berries W):= prime (fun c=> handy d' (Tset n) (X₁ (i,c)) (Y' (i,c)))
    change Yep _ _ _ (Real.exp _ * η⁻¹^(12*(W.length*k)+l')*F₀^(W.length*k)*‖G'‖)
    have hk:H.length=W.length*k:=by unfold H fir; rw [List.length_product]; simp
    have hx':probe W v=fo Z₁ H:=packsProd Z₁ v hx
    rw [hx',←hk]; apply (Pledge.beam (A:=fun i c=> X₁ (i,c)) (Y':=fun i c=>Y (i,c)) (Z':=fun i c=> Y' (i,c)) (b:=d') hP b b' r r' (show 0<R+4-3 by linarith) (show 1 ≤ 2+R by linarith) (fun i c=> uX _) (fun i c=> vX _) (fun i c=> qF _) (fun i c=> q₀ _) ?_ ?_ ?_ ?_ G' (Window.fine_enlarge (subset_univ _) hG) (fun i j=> comm_lost hG.sector (u₀ _)) H (hp.attach.product (List.nodup_ofFn_ofInjective injective_id)) h hη.1 hη.2).weigh ?_ (by have eO:=hη.1; positivity)
    · intro i j; apply (hF (i,j)).trans; have he: e^3 ≤ 1:= pow_le_one₀ r.le r'; linarith
    · intro i c j h; change inner ℂ (Y (i,c)) (X₁ (j,h))=_; rw [←inner_conj_symm,hY]; by_cases w:(i,c)=(j,h); · have e:i=j ∧ c=h:= Prod.mk.inj w; rcases e with ⟨rfl,rfl⟩; simp
      by_cases u:i=j ∧ c=h; · obtain ⟨rfl,rfl⟩:=u; exact (w rfl).elim
      rw [if_neg u,if_neg (Ne.symm w)]; simp -- tune ordering
    · intro i j l k h; rw [←inner_conj_symm,ht',if_neg ?_]; simp; intro k; exact h.elim (fun x=>x (Prod.mk.inj k.symm).1) (fun x=>x (Prod.mk.inj k.symm).2)
    · intro i j; exact (norm_sub_le ..).trans ((add_le_add (show ‖(1:FC (Single n))‖ ≤ 1 by simp) (Perron.peakCost _ _ (vX (i,j)) (h₁ _))).trans_eq (by ring))
    exact le_of_eq (by unfold F₀ meridiem; ring)

set_option maxHeartbeats 250000 in
lemma iced {A0:Orbit n→ Pane n}(h:Company j M w d c t γ γ' τ ε R L)(p:0<R)
    (u:ℝ)(l:ℕ)(P:Roof n u δ' l A0)(s:τ≤u)(q:l+c ≤ t)
    (S:Sparkle n δ' M j)(v:0≤δ)(y:δ'≤δ)
    {κ ε' C:ℝ}(A:Winter j δ n γ w κ)(A':Winter j δ n γ' c ε')(U:∀ (i:Finset (Seat n)),Sparse d i→∀ b,HearthB C (sp b j M (1:Pane n)) i)(x:κ*C≤1/3)
    (e:ℝ)(r:0<e)(r':e ≤ 1)(g:(ε'*R+ε)+2*C*(ε'*R+ε) ≤ e^3)
    {η:ℝ}(hη:0<η ∧ η≤1) (Z:ℝ)(hp:5*(e*(R+4)*meridiem R)≤Real.exp (-2*(Z+meridiem R-12*Real.log η)))(ht:0≤Z)(k':0<k)
    (X:Orbit n)(Φ Θ:Wave (Single n))(b:Sea (spar j M (A0 X)) Φ)(b':Sea (cutM (Tset n)) Θ) : Yep (η⁻¹*e⁻¹) (acts (star (probe L (X.1,A0 X))) Θ) Φ (Real.exp (crater (cutM (Tset n)) (spar j M (A0 X)) η + -(Z*(L.length*k:ℕ)) + ((Z+meridiem R-12*Real.log η)*(4*(t+t+1)^4*k:ℕ))*flakes τ X.1)):=by
 classical
 obtain ⟨W,G,d',u',kG,tWG,kL,v₀,F⟩:= orders k' h X.1; let f:Fields n := (X.1,A0 X); let P':= h.shorter u'; let Q:= h.shorter kG; let G':= probe G f
 have hu(i)(p:i∈W):i.rev=d' ∧ i.feel τ t f.1 ∧ Agrees (hot i c) f.2 f.1:=by
    obtain ⟨ht,hp⟩:= F i p; refine ⟨hp,ht,Py.Rate.Pannier.fledged P (hot i c) X s ?_⟩; apply Finset.disjoint_left.mpr; intro x ht' v; obtain ⟨y,w,h₀⟩:=halo_spec.mp ht'; obtain ⟨j,u,g⟩:=halo_spec.mp w; exact disjoint_left.mp ht (halo_spec.mpr ⟨j,u,(separation_triangle j y x).trans (by omega)⟩) v
 obtain ⟨X₁,Y,Y',uX,vX,qF,hF,u₀,q₀,hY,ht',h₁,h₂⟩:= assemblage (v:=f) P' S A v (P.paid X) y A' (fun i g=> U i g d') x g hu (whereV G) tWG.symm
 let F₀:=5*(e*(R+4)*meridiem R);  have hT:0≤ meridiem R:=by unfold meridiem; positivity
 let C':= Z+meridiem R- 12* Real.log η
 let ζ:= crater (cutM (Tset n)) (spar j M (A0 X)) η
 have hG: Fine (Tset n) (modesIn n (whereV G)) false G':= Q.corsage.allV f
 have hc':L.length*k=W.length*k+G.length*k:=by
    rw [show L.length=W.length+G.length from kL.length_eq.trans List.length_append, Nat.add_mul]
 let K:=L.length*k
 have He: Yep (η⁻¹*e⁻¹) (acts (star (probe L f)) Θ) Φ (Real.exp ζ*η⁻¹^(12*K)*F₀^(W.length*k)*‖G'‖):=by
    rw [prod_perm h kL f k',probe_combine,Pi.mul_apply]; unfold K; rw [hc',mul_add];
    exact enlist p e r r' (S.projection _ (P.paid X)) b b' uX vX qF hF u₀ q₀ hY ‹∀ i l,inner ℂ (X₁ i) (Y' l)= if i=l then 1 else 0› h₁ hG f h₂ (P'.nodup k') (Q.costL f) hη

 have hR:0≤F₀:=by unfold F₀; positivity
 apply He.weigh _ (by have ht:=hη.1; positivity)
 rw [←Real.exp_log (inv_pos.mpr hη.1),Real.log_inv, ←Real.exp_nat_mul]; rw [Real.exp_add,Real.exp_add]; simp only [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
 let I:=W.length*k; let R':=meridiem R
 apply (mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ hR hp I) (le_trans (Q.bill p.le f) (le_trans (pow_le_pow_right₀ (by linarith only [hT]) (Nat.mul_le_mul_right _ kG.length_le)) (pow_le_pow_left₀ (show 0 ≤ 1+R' by unfold R'; positivity) (show 1+R' ≤ Real.exp R' by linarith only [Real.add_one_le_exp R']) K))) (norm_nonneg _) (by positivity)) (Real.exp_pos _).le).trans
 rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add,←Real.exp_add]; apply Real.exp_le_exp_of_le
 have he:0 ≤ C':=by unfold C'; linarith [Real.log_nonpos hη.1.le hη.2]
 let D₀:= (roughness τ X.1).card*(4*(t+t+1)^4*k)
 have hc:(K:ℝ) ≤ 2*(I:ℝ)+D₀:=by
    have hv: K ≤ 2*I+D₀:= le_trans (Nat.mul_le_mul_right k v₀) (le_of_eq (by unfold I D₀; ring)); exact_mod_cast hv
 have hw:C'=Z+R'-12*Real.log η:=rfl
 have hx:(↑D₀:ℝ)= (↑(4*(t+t+1)^4*k:ℕ):ℝ)*flakes τ X.1:= by unfold flakes D₀; push_cast; ring
 -- work cast. avoid simp all
 change (↑(12*K:ℕ):ℝ)*(-Real.log η)+( (I:ℝ)* (-2*C')+(K:ℝ)* R') ≤ -(Z*(K:ℝ))+C'*((↑(4*((t+t+1)^4*k):ℕ):ℝ)*flakes τ X.1)
 rw [←mul_assoc 4 ((t+t+1)^4) k, ←hx]; rw [Nat.cast_mul]; norm_num only [Nat.cast_ofNat] -- tune
 nlinarith only [mul_le_mul_of_nonneg_left hc he,show C'*K=(Z+R'-12*Real.log η)*K from congrArg (·*((K:ℕ):ℝ)) hw]
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.iced
