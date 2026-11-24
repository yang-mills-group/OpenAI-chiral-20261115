import YM.CF.Dial.Moose
/-! Single-lattice specialization. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
def idrat(N:Side):Ratio N N:=⟨1,by simp⟩
variable {N P:Side}
lemma one_side(G:Ratio N P)(h:G.count=1): P=N:=Subtype.ext (G.exact_size.trans (by rw [h]; exact Nat.mul_one _))
lemma idr(G:Ratio N N)(h:G.count=1): G=idrat N:=by cases G with | mk a b=> congr; -- tune
lemma glass (x:Site N): (idrat N).embed x=x:=by rw [Ratio.embed]; simpa [idrat]
lemma filed(i:Site (More N)): (ratio (idrat N)).embed i=i:=by rw [idr (ratio (idrat N)) rfl]; exact glass _
lemma jamN(r: Site (idrat N).count): r=0:=by funext i; change r i=(0:ZMod 1); exact @Subsingleton.elim (ZMod 1) _ _ _
lemma isle_back (i:Site N)(r:Site (idrat N).count): isle (idrat N) (i,r)=i:=by rw [jamN r,isle_apply,glass]; rw [show lift (0:Site (idrat N).count)=0 from by simp,show offset (idrat N).count=0 from (by funext i; simp [offset,idrat,mid])]; simp
lemma chairs (G: Ratio N P)(u:Bool)(e:ℝ)(h:G.count=1): rope G (u,true) e=rope G (true,true) e:=by
  rcases one_side G h; rw [idr G h];
  have he:{x y:Tag (curveD (idrat N) e)}→ x.run=y.run→x=y:=by rintro ⟨x,h⟩ ⟨y,g⟩ eq; simp at eq; congr
  apply he; cases u; swap; rfl
  funext g; apply Subtype.ext; let R:=idrat N
  change ((rod R false e).run _).val=((rod R true e).run _).val; rw [hatch,hatch]
  congr 1; funext i; unfold harborT; change (coinK (g ((ratio R).embed (node i.1)))).val=(coinK (g (node (isle R (i.1,i.2))))).val
  rw [filed,isle_back]
lemma jointly (U:Bkg (More N)) {e:ℝ} (p:Cube.Guard U e)(h:0<e): JointB (idrat N) (U,U) e:=by
  refine ⟨p,p,fun i=>?_⟩; rw [filed]; rcases i with ⟨x,i⟩; rw [show pathL (idrat N) i=[posDir i] from rfl]; simpa [travel,Step.pos_read] using h.le
lemma chord_same (x:Sew N N): squareD (idrat N) false (post x)=boots (idrat N) (postC x.2.2):=by
  let G:=idrat N
  unfold squareD; ext ⟨⟨i,r,b⟩,v⟩ ⟨⟨j,t,c⟩,w⟩; rw [jamN r,jamN t];
  change (jump (Equiv.refl _) _) ((i,0),b,v) ((j,0),c,w)=postC x.2.2 ((isle G (i,0),b),v) ((isle G (j,0),c),w)
  rw [isle_back,isle_back,← summit_p]; rfl
variable (j:ℕ)(hp:1≤j)
def repeated(j:ℕ):Chop Male:=mateF (foal j true)
include hp
lemma strut(u v:Bool): BoxD 1 (u,true) (v,true) (repeated j):=by
  have ht : BoxD 1 (true,true) (true,true) (repeated j) := BoxD.marked (flowers _ (funde_s _ hp))
  obtain ⟨a,c,e,h,k,m,n,H⟩:=ht; exact boxify (e:=e) (k:=n) (C:=c) (fun i _ _ G hc hg=> by rw [chairs G u e hc,chairs G v e hc]; exact H i G hc hg) h m
lemma festival (L:Side):Still L fun G x=>∀ i, let U:= (unionP x.1); IsStarProjection (skewE j i true _ U.1) ∧ IsStarProjection (skewE j i true _ U.2):=by -- U.1 type stem→ infer N? explicit
  obtain ⟨a,h,r,F⟩:=funde_q j hp; refine ⟨a,h,r,fun {N P} G he hv x p i=>?_⟩
  exact ⟨F i _ (by rw [G.exact_size]; exact le_trans hv (Nat.le_mul_of_pos_right _ G.count.property)) _ p.covW.fg,F i _ hv _ p.covW.cg⟩
lemma monoto : Land 1 (repeated j) (repeated j) (repeated j):=by
  refine ⟨strut j hp _ _,strut j hp _ _,strut j hp _ _, fun i _ _ G he=> ?_,(festival j hp 1).forward ?_⟩ -- hp implicit?
  · exact ⟨homeT G j i true hp,homeT G j i true hp⟩
  intro N P G hc U H i; have h : IsStarProjection (repeated j i G (post U)):= carts_p (switchG G).symm (H i).1
  exact ⟨h,h.isIdempotentElem.eq,h.isIdempotentElem.eq⟩
lemma match_ci(x:Sew N N)(M:Male){m:ℕ} (p0: IsStarProjection (skewE j M true N (post x).1.1))(h:let P:=repeated j M (idrat N) (post x); let B:=tonic (repeated j) (repeated j) M (idrat N) (post x); let C:=squareD (idrat N) false (post x); let V:=squareD (idrat N) true (post x)
    (earnings (repeated j) (repeated j) m M (idrat N) (post x)).trace= rockZ B P m m ∧ Complex.exp (rockZ B P m m) • filled P C=filled P (P*V*Pᵀ) ∧ filled P C≠0):
 let P:= skewE j M true N (post x).1.1; let H:=filled P (postC x.2.1); let K:=filled P (postC x.2.2)
 Complex.exp ((earnings (repeated j) (repeated j) m M (idrat N) (post x)).trace) • K = H ∧ K≠0 ∧ H≠0:=by
  intro P H K; let G:=idrat N; let R:= repeated j; let B:=R M G (post x); let V:=squareD G true (post x); let C:=squareD G false (post x); let s:= (earnings R R m M G (post x)).trace
  have he:IsStarProjection B:=carts_p (switchG G).symm p0
  obtain ⟨ht,h1,h2⟩:=h
  have hs:=fun (y:Stun N)=>relabelF (switchG G).symm (starC (hook y ∘ node) (fun _=>hookN ..)) p0;
  let A:= cartsL (switchG G).symm
  have hK:filled B C=A K:=by unfold C; rw [chord_same]; exact hs x.2.2
  have hH:filled B V=A H:=by unfold V; rw [square_true]; exact hs x.2.1
  have hy:filled B (B*V*Bᵀ)=filled B V:=by rw [filled,←pair_cov,←act_mul,quant_line he]; rfl
  have hz: K≠0:=by
    intro p; apply h2; change filled B C=0; rw [hK,p]; exact map_zero (hoist _ _)
  suffices hx: Complex.exp s • K= H from ⟨hx,hz,hx ▸ smul_ne_zero (Complex.exp_ne_zero _) hz⟩
  apply carts_inj (switchG G).symm; rw [carts_s]; change Complex.exp s • A K=A H; rw [←hK,←hH]
  have he': s= _:= ht; rw [he']; exact (Eq.trans h1 hy)
end YM.CF.Dial
