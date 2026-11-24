import YM.CF.Dial.Head
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
def brush(x:Spool N): Spool N:=fun i u=> star (x i (!u))
lemma brush_p(X:Stun N):brush (palt X)=palt X:=by funext x u; cases u<;> simp [palt,brush]
def chargeB(x:Bale N P): Bale N P:=(icec x.1,brush x.2.1,brush x.2.2)
lemma charge_p(x:Sew N P): chargeB (post x)=post x:=by rw [post,chargeB,revI,brush_p,brush_p]
lemma brush_eq(x y:Spool N)(i): ‖brush x i-brush y i‖=‖x i-y i‖:=by
  apply le_antisymm<;> refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k=> ?_
  · change ‖star (x i (!k))-star (y i (!k))‖≤_; rw [←star_sub,norm_star]; exact norm_le_pi_norm (x i-y i) _
  have h:=norm_le_pi_norm (brush x i-brush y i) (!k); rw [Pi.sub_apply,brush, brush,Bool.not_not,←star_sub,norm_star] at h; exact h
lemma brush_norm(x y:Spool N): ‖brush x-brush y‖=‖x-y‖:=by
  apply le_antisymm<;> refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun q=> ?_
  · exact (brush_eq _ _ _).le.trans (norm_le_pi_norm (x-y) q)
  exact (brush_eq _ _ _).ge.trans (norm_le_pi_norm (brush x-brush y) q)
lemma brush_heat(x:Spool N)(g:Site (More N)→E): brush (heat g x)= heat g (brush x):=by funext i u; cases u<;> simp [brush,heat,mul_assoc]
lemma charge_n(x y:Bale N P): ‖chargeB x-chargeB y‖=‖x-y‖:=by simp only [chargeB,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,brush_norm,icec,ice_norm]
lemma charge_t (x y:Bale N P)(S:Seal (Site (More P))):bookK G (chargeB x) (chargeB y) S=bookK G x y S:=by simp only [chargeB,bookK,brush_eq,deal,icec,ice_f]
lemma frozen_g (x:Bale N P)(g:Site (More P)→E): chargeB (novel G g x)=novel G g (chargeB x):=by rw [chargeB,novel,novel,chargeB]; simp only [jazzI,brush_heat] -- tune
lemma frozen_p(x: Bale N P) {e:ℝ}(p:x∈zoneP G e):chargeB x∈zoneP G e:=by obtain ⟨U,h,f⟩:=p; exact ⟨U,h,(by rwa [←charge_p,charge_n])⟩
lemma coatD {V:Set ℂ} (h:IsOpen V)(x:ℂ→Spool N)(hx:DifferentiableOn ℂ x V): DifferentiableOn ℂ (fun i=> brush (x (star i))) (star ⁻¹' V) :=by
  intro i g
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_pi.mpr; intro j; apply differentiableAt_pi.mpr; intro k
  let f (i:ℂ):= x i j (!k)
  have hp: DifferentiableAt ℂ f (star i):=differentiableAt_pi.mp (differentiableAt_pi.mp (hx.differentiableAt (h.mem_nhds g)) j) _
  exact differentiableAt_star_conj_iff.mpr hp
variable {ι:Type*}{A:Chop ι}{L:Side}{u v:AxisT}{a c e:ℝ}
def billS (e:ℝ):TopK G e→ TopK G e:= fun x=>⟨chargeB x.val,frozen_p G x.val x.property⟩
lemma stance_v(e:ℝ): Towards (curveD G e) (badge _) (curveD G e) (badge _) id 1:=⟨continuous_id,rfl,rfl,fun i j=>rfl,fun S i j=> by rw [one_mul]; exact le_rfl, fun f h=> h⟩ -- remove
lemma ct_brush(e:ℝ):Continuous (billS G e):=by unfold billS chargeB brush icec ice; fun_prop
lemma cc_g(e:ℝ)(t:Site (More P)→E)(x):billS G e ((curveD G e).drive t x)=(curveD G e).drive t (billS G e x) := Subtype.ext (frozen_g G _ _)
lemma cc_q(e:ℝ) {f:TopK G e→ℂ}(p:(badge _).valid f): (badge (zoneP G e)).valid fun x=> star (f (billS G e x)) := by
  apply realigns p; intro V h γ p
  let T:= fun z:ℂ=> (γ z).val
  exact ((snowy h (fun z=>(T z).1.1) p.fst.fst).prodMk (snowy h (fun z=>(T z).1.2) p.fst.snd)).prodMk ((coatD h (fun z=>(T z).2.1) p.snd.fst).prodMk (coatD h (fun z=>(T z).2.2) p.snd.snd))
lemma cscale(x y:TopK G e)(S:Seal (Site (More P))): (curveD G e).eval S (billS G e x) (billS G e y)=(curveD G e).eval S x y:= congrArg (· / |e|) (charge_t G _ _ S)
lemma back_h(A:Raw (TopK G e) (Iota G))(p:Crown (badge _) (rope G u e) (rope G v e) a c A): Crown (badge _) (rope G (upright u) e) (rope G (upright v) e) a c (fun x=>cc (A (billS G e x))) :=by
  obtain ⟨F,C,h,q,r⟩:=p
  rw [ropes_cc,ropes_cc]; let B:=billS G e;
  refine ⟨fun S x=>cc (F S (billS G e x)),C,fun S=> ?_,q,fun x=>?_⟩
  · have he :Ticket (rope G u e) (rope G v e) S (C S) (fun x=>F S (B x)):=by
      refine ⟨fun g i=> (by unfold B; rw [cc_g]; exact (h S).frame g (B i)),fun i j=>?_⟩
      have ht:= (h S).expo i j; exact ⟨ht.positive, ht.triggered,fun i=> ht.bounded _, fun x y=> by
        have he:= ht.variation (B x) (B y); rw [cscale] at he; exact he, ht.connected.comp (ct_brush G e)⟩
    exact ⟨he.ccT,fun i j=> cc_q _ _ ((h S).fuel i j)⟩
  dsimp only; rw [r]; ext; simp [Matrix.sum_apply]
lemma BoxD.balm(h:BoxD L u v A): BoxD L v u (fun i _ _ G x=>star (A i G (chargeB x))) :=by
  obtain ⟨a,c,e,h,r,f,k,H⟩:=h; exact boxify (k:=k) (fun i _ _ G he hk=> (H i G he hk).impose (billS G e) (ct_brush G e) (cc_g G e) (fun S x y=>cscale G x y S) (fun _=>cc_q G e)) h f
lemma BoxD.abrade(h:BoxD L u v A): BoxD L (upright u) (upright v) (fun i _ _ G x=>cc (A i G (chargeB x))):=by
  obtain ⟨a,c,e,h,r,f,k,H⟩:=h; exact boxify (k:=k) (fun i _ _ G he hk=>back_h G _ (H i G he hk)) h f
lemma cc_sq (x:Bale N P): chargeB (chargeB x)=x:=by
  have ht {N:Side}(x:Stem N): ice (ice x)=x:=by funext i u; simp [ice]
  have he {N:Side}(y:Spool N): brush (brush y)=y:=by funext i u; simp [brush]
  simp [chargeB,brush_eq,he,icec, ht]
lemma BoxD.tail(h:BoxD L u v A): BoxD L (upright v) (upright u) (fun i _ _ G x=> (A i G x)ᵀ):=by
  have hp:=h.balm.abrade; simp only [cc_sq, cc,star_star] at hp; exact hp
end YM.CF.Dial
