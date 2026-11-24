import YM.CF.BPress.Spin.Hue
/-! A∙C-C∙ccA under arbitrary small speed. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Fock SU SU.Pair Lat Lattice Cube Tenant Branch Tulip Scroll Dial Thera Paint Eye Nacre Pledge Push.AbsoluteSums.Paths
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {s N:Side}

def Bend (P:Paint s)(U:Bkg s)(v:ℝ): Prop:=∀ x i, ‖P x- swivelC (U (x,i)) (P (x+step i))‖ ≤ v
namespace Bend
variable {P:Paint s}{U:Bkg s}{v a b ε :ℝ}
lemma turn (h:Bend P U v)(f:Site s→E): Bend (rotateC f P) (gauge f U) v:=fun x i=> by simp only [rotateC,Lattice.gauge, ←turn_add  ]; simp; rw [turn_add,Paint.iso]; exact h x i
lemma mono (h:Bend P U v)(p:v≤a): Bend P U a:=fun x i=> (h x i).trans p
lemma path (h:Bend P U v)(x:Site s)(w:Walk): ‖P x-swivelC (travel U x w) (P (stop x w))‖≤w.length*v:=by
 induction w generalizing x with
 | nil=> simp [travel,stop,turn_one]
 | cons i w ih=>
   have hf:‖P x-swivelC (i.read U x) (P (x+i.vec))‖ ≤ v:=by
    rcases i with ⟨k,t⟩; cases t; exact h x k
    simp only [Step.vec,Step.read, Step.used,ite_true, ←sub_eq_add_neg]; rw [← Paint.iso (U (x-step k,k)),←turn_add,mul_inv_cancel,turn_one,norm_sub_rev (swivelC (U (x-step k,k)) (P x))]; have he:=h (x-step k) k; rw [sub_add_cancel] at he; exact he
   let y:=x+i.vec; let g:=i.read U x; rw [travel, turn_add]; apply (norm_sub_le_norm_sub_add_norm_sub _ (swivelC g (P y)) _).trans; refine (add_le_add (d:=w.length*v) hf ?_).trans_eq ?_; unfold g; rw [Paint.iso]; exact ih y; rw [List.length_cons]; push_cast; ring
lemma moving (U:E)(A:Op Slot) : ‖swivelC U A-A‖≤2*sphereRate*chord U 1*‖A‖:=by
 let V:=matter U; let r:=sphereRate*chord U 1; let W:=ccU V; change ‖congrC V A-A‖≤_; rw [congr_form]; apply (norm_sub_le_norm_sub_add_norm_sub _ (A*star W.val) _).trans
 have ht: ‖V.val-1‖≤r:=by have he:=sphereRate_cost.bot U 1; rw [map_one] at he; exact he -- tune
 have hq: ‖star W.val-1‖ ≤r:=by rw [show star W.val-1=star (cc (V.val-1)) by simp; rfl, norm_star]; rw [norm_cc]; exact ht -- name
 rw [←sub_mul, show ‖(V.val*A-A)*star (ccU V).val‖=‖V.val*A-A‖ from CStarRing.norm_mul_coe_unitary _ (star (ccU V)),show V.val*A-A=(V.val-1)*A by rw [sub_mul,one_mul],show A*star W.val-A=A*(star W.val-1) by rw [mul_sub,mul_one]]; refine (add_le_add ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))) ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left hq (norm_nonneg _)))).trans_eq ?_; unfold r; ring
lemma vac_path (h:Bend P U v)(p:MatLite P 1)(x:Site s)(w:Walk)(f:0≤a)(t:chord.Close U 1 (native x w) a): ‖P x-P (stop x w)‖≤w.length*(v+2*sphereRate*a):=by
 let g:= travel U x w; have hx :∀ w:Walk,∀ x:Site s,travel (1:Bkg s) x w=1:=fun w=>by induction w with|nil=>simp [travel]|cons i w ih=>simp [travel,Step.read,ih]
 have he:=chord.path U 1 w x a t; rw [hx] at he; let A:=P (stop x w); apply (norm_sub_le_norm_sub_add_norm_sub _ (swivelC g A) _).trans; apply (add_le_add (h.path x w) ((moving g A).trans ((mul_le_of_le_one_right (mul_nonneg (mul_nonneg (by norm_num) sphereRate_cost.positive.le) (chord.positive ..)) (p _)).trans (mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num) sphereRate_cost.positive.le))))).trans_eq; ring
lemma vac_member (h:Bend P U v)(p:MatLite P 1)(g:0≤v)(f:0≤a){w:ℕ} (z:Site s)(H:chord.Close U 1 (bay (terr s) z (4*w)) a) (x:Site s)(e: x∈ bay (terr s) z w): ‖P x-P z‖≤4*w*(v+2*sphereRate*a):=by
 let W:= Font.shiftH z x; have hx: W.length≤4*w:= (Font.short z x).trans (Nat.mul_le_mul_left _ ((bay_mem _).mp e))
 have ht:= h.vac_path p z W f (chord.Close.smaller _ _ (fun i hi=> (bay_mem _).mpr ((to_ball z W hi).trans hx)) H); rw [Font.stopH z x] at ht -- tune
 rw [norm_sub_rev]; apply ht.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hx) (by have he:=sphereRate_cost.positive; positivity)) -- tune
end Bend

def wash {I:Type*}[Fintype I][DecidableEq I](A B: Op I):=A*B-B*cc A
def washPrice (P Q:Pledge):=(P.times Q).plus (Q.times P)
lemma washP {I D X:Type}[TopologicalSpace D][Fintype X][DecidableEq X][Fintype I][DecidableEq I]{P Q:Pledge}{b:Stage X I D Empty}{f g:Raw D I}(h:P.Costs b f)(p:Q.Costs b g): (washPrice P Q).Costs b (fun x=>wash (f x) (g x)):= Costs.sub (Costs.mul h p) (Costs.mul p (Costs.stars h))
lemma wash_u {I:Type*}[Fintype I][DecidableEq I](A B:Op I)(U:UNI I): wash (twist U A) (congrC U B) = congrC U (wash A B):=by
 let V:= ccU U; have he:∀ A B:Op I,U.val*A*star U.val*(U.val*B*star V.val)= U.val*(A*B)*star V.val:= fun A B=>by
    rw [mul_assoc (U.val*A), ←mul_assoc (star U.val), ←mul_assoc (star U.val), U.property.1,one_mul]; simp only [mul_assoc]
 have hg:∀ A B:Op I,U.val*A*star V.val*(V.val* B*star V.val)= U.val*(A*B)*star V.val := fun A B=>by
    rw [mul_assoc (U.val*A), ←mul_assoc (star V.val), ←mul_assoc (star V.val), V.property.1,one_mul]; simp only [mul_assoc]
 rw [wash, congr_form,cc_twist,twist_formula,twist_formula,he,hg]; rw [congr_form,wash,mul_sub,sub_mul]
def HueSpace (N:Side)(d:ℝ) := OpenW N d × {x:Paint (More N)//MatPlan x}
-- use abbrev
abbrev Suit (N:Side)(d:ℝ):= OpenW N d × {x:Paint (More N)//MatPlan x}

def payHue (P K: Paint s)(X:Support s):= ∑ x∈X, ‖P x-K x‖
namespace Crystal
variable {d ε q:ℝ} {j v:ℕ} {P:Pledge}
def unit_stage (N:Side)(d:ℝ):Form N (Suit N d):= {
 eval S x y:= invitation S x.1.val y.1.val + payHue x.2.val y.2.val S
 pos S x y:= add_nonneg invitation.positive (sum_nonneg (fun x _=>norm_nonneg _))
 mono h x y:= add_le_add (invitation.mono h) (sum_le_sum_of_subset_of_nonneg h (fun _ _ _=>norm_nonneg _)) }
theorem suit_p (h:Shelf N d j P)(M:Jill.Male): Form.Comes (unit_stage N d) (washPrice P (stream 1)) (fun x=> wash (spar j M x.1.val) (coupling x.2.val)):=by
 let F:= unit_stage N d; have ht := Form.pulls (h.entries M) Prod.fst continuous_fst (F':=F) (fun s x y=> le_add_of_nonneg_right (sum_nonneg (fun _ _=> norm_nonneg _))); refine washP ht (stream_cost F (fun x:Suit N d=> x.2.val) (fun x=> MatPlan.one x.2.property) (continuous_subtype_val.comp continuous_snd) ?_)
 intro S x y i hi; exact (single_le_sum (f:=fun i=> ‖x.2.val i-y.2.val i‖) (fun _ _=> norm_nonneg _) hi).trans (le_add_of_nonneg_left invitation.positive)

-- purchase the single-neighbour speed threshold (can take further smaller positive d after using). Numeric costs uniform w fixed after P.
def hBill (q:ℝ)(n:ℕ):= 4*ν n^4*(sphereRate*priceF (4*n) q)+ν n^4*(4*n*(q+2*sphereRate*(sphereRate*priceF (4*n) q)))
lemma patch_cost (d:ℝ)(H:0<d)(p:d≤q)(U:Bkg (More N))(u: Cube.Guard U d)(K:Paint (More N))(t:MatPlan K)(z:Site (More N))(v:ℕ)(g:Bend K U q)(f:2*(4*v)+2<(More N).val):let F:=hue U z; let W: Suit N d:= (⟨gauge F U,u.cov F⟩,⟨rotateC F K, fun x=> turn_plan (t x) (F x)⟩); let Z: Suit N d:=(⟨1,guard0 H.le⟩,⟨fun _=>W.2.val z,fun _=> W.2.property z⟩); (unit_stage N d).eval (bay (terr (More N)) z v) W Z ≤ hBill q v :=by
 intro F W Z; let b:=terr (More N); let S:=bay b z v; let X:= W.2.val; let c:=sphereRate*priceF (4*v) q; have hj:=H.trans_le p; have hv:=sphereRate_cost.positive; have hc:0≤c:=by unfold c priceF; positivity
 have hr : Cube.Guard (gauge F U) q:= (u.cov F).shrink p; have hT:chord.Close W.1.val 1 (bay b z (4*v)) c:=by -- gauge_light yields using original q Guard
    exact invitation.gauge_uniform sphereRate_cost _ f q hj.le (u.shrink p) z
 have he (x)(hx:x∈ S): ‖X x - X z‖≤ 4*v*(q+2*sphereRate*c):= Bend.vac_member (g.turn F) (MatPlan.one W.2.property) hj.le hc z hT x hx
 have hk : (S.card:ℝ)= ν v^4:=by unfold S b; rw [volume z (by omega)]; unfold ν; push_cast; ring
 apply add_le_add
 · apply le_trans (invitation.size (U:=W.1.val) hc (V:=(1:Bkg (More N))) (S:=S) (chord.Close.smaller _ _ (fun i hi=> (bay_mem _).mpr ((bay_mem _ |>.mp hi).trans (by omega))) hT)); rw [hk]
 apply (sum_le_sum (fun x hx=> he x hx)).trans_eq; rw [sum_const,nsmul_eq_mul,hk]
lemma hBuy (n:ℕ)(h:0<ε): ∃ q:ℝ,0<q ∧ hBill q n ≤ ε:=by
 have ht:0< hBill 1 n := by unfold hBill priceF; have he:=sphereRate_cost.positive; have hp:=(vol_pos (w:=n)); positivity
 let q:= ε/hBill 1 n; refine ⟨q, div_pos h ht, (le_trans ?_ (ge_of_eq (show ε=hBill 1 n*q from Eq.symm (mul_div_cancel₀ _ ht.ne'))))⟩
 apply le_of_eq; unfold hBill priceF; ring

-- uniform w geometry. Main raw grant before use at tilted A.
theorem rawSpeed (P:Pledge)(p:0<ε)(j:ℕ)(h:1≤j): ∃(q:ℝ)(v:ℕ),0<q∧∀ N:Side,v≤ N.val→∀ d:ℝ,0<d→d≤q→Shelf N d j P→∀ U:Bkg (More N),Cube.Guard U d→∀ M:Jill.Male,∀H:Paint (More N),MatPlan H→ Bend H U q→‖wash (spar j M U) (coupling H)‖≤ ε:=by
 let a:=ε/2; have ha:0<a:=half_pos p; let E:=washPrice P (stream 1); obtain ⟨w,m,r⟩:= (pledge_lift E ha.le (half_lt_self p)).exists; obtain ⟨k,b,B,X⟩:=latticeFieldEstimates_price E ha
 obtain ⟨q,u,U⟩:=hBuy (w+k) B; refine ⟨q,m+8*(w+k)+3,u,?_⟩; intro N L d T K Y g F M H t l
 let S:=unit_stage N d; let G: Suit N d→ Op (Single N):= fun x=> wash (spar j M x.1.val) (coupling x.2.val); let f: Suit N d:=(⟨g,F⟩, ⟨H,t⟩)
 have he:(More N).val=N.val*2:=rfl; refine r (More N) (by omega) (b:=S.stage) rfl G (suit_p Y M) f (fun z=>?_); let σ:=hue g z; let A:= bay (terr (More N)) z w; let J:=look (home N) A
 let W:Suit N d:=(⟨gauge σ g,F.cov _⟩,⟨rotateC σ H,fun x=> turn_plan (t x) (σ x)⟩); let V:Suit N d:=(⟨1,guard0 T.le⟩,⟨fun _=> W.2.val z, fun _=> W.2.property _⟩)
 have hp(G' : Op (Single N)): ‖J*congrC (tradew N σ) G'‖=‖J*G'‖:=by rw [congr_form]; exact gauge_norm σ (bail N 1) ((bail N 1).reverseV) A G'
 have hv:G V=0:= sub_eq_zero.mpr (free_anti j h M (W.2.val z))
 have hx : ‖J*(G W-G V)‖≤a:= X (suit_p Y M) W V A (include_patch _ rfl W V (k:=k) ((patch_cost d T K g F H t z _ l (by omega)).trans U))
 have ht:G W=congrC (tradew N σ) (G f):=by unfold G; change wash (spar j M (gauge σ g)) (coupling (rotateC σ H))=_; rw [coupe_gauge,Y.tag M (⟨g,F⟩:OpenW N d), wash_u] -- tune
 rwa [hv,sub_zero,ht,hp] at hx
end Crystal
end YM.CF.BPress.Spin
