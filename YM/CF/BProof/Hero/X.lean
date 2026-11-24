import YM.CF.BProof.Hero.Bill
import YM.CF.BProof.Grid.Skeleton
import YM.CF.BProof.Angular.Plaque
/-! Cubical speed relative Fill. Preserve even custom subcomplexes in B-marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hero
open Function Dream Cube Spin Extension Filter Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators NNReal ENNReal
attribute [local instance] opCStarAlgebra

def XF : Grid.Fiber 4 SU.group Ballot where
 cost := Xd
 symm x y:= norm_sub_rev ..
 self x:=by simp [Xd]
 triangle:=Xd_triangle
 C:= xm
 C_one:=xm_low
 diameter :=Xd_h
 move:= scaledV
 unit:=fun x=> congrFun scaled_one _
 mul:= scaled_seq
 isom:=scale_dist_t
 pace:=Xd_rate
 cont_d:=by unfold Xd; change Continuous (fun z:Ballot × Ballot=>‖z.1.val-z.2.val‖); fun_prop
 cont_a:= scaled_cont
 extend K p:=by
    obtain ⟨L,h,H⟩:=Extension.sphere_extend (X:=Fin 4→ℝ) (Y:=Vect) 1 1 K one_pos one_pos p
    refine ⟨L,h,fun S T f s t h' hh=>?_⟩; let Y(x:Fin 4→ℝ):=(f x).val; let P:Submodule ℝ Vect:=⊤
    obtain ⟨g,v,hg,H⟩:= H S T (fun _=>P) Y s t h' (fun _ _=>by rw [show Module.finrank ℝ P=10 from finrank_top ℝ Vect |>.trans Cube.dim_vect]; simp) (fun _ _ _ _=> by rw [sub_self,norm_zero]; positivity) (fun i _=>⟨vote_unit _, Submodule.mem_top⟩) hh
    let G(x:Fin 4→ℝ):Ballot:= if h:x∈ S then ⟨g x,by simp [Sphere,(hg x h).1]⟩ else apex; have he(x)(hx:x∈S): (G x).val=g x:= by simp [G,hx]
    refine ⟨G,fun x hx=>Subtype.ext (by rw [he _ (t hx)]; exact v hx), fun x hx y hy=>?_⟩; unfold Xd; rw [he _ hx, he _ hy]; exact H _ hx _ hy
variable {c s:Side}(g:Ratio c s)
def can (e:ℝ)(r:Side):= XF.pay 4/r.val ≤ e
lemma X_pay:0<XF.pay 4:= Grid.Fiber.pay_p ..
lemma buyX(e:ℝ)(p:0<e): ∃ r:Side,can e r:=by
 obtain ⟨n,hn⟩:= exists_nat_gt (XF.pay 4/e); let r:Side:=⟨n+1,by omega⟩; have ht: XF.pay 4/e≤(r.val:ℝ):=hn.le.trans (by exact_mod_cast n.le_succ); have hr: (0:ℝ)<(r.val:ℝ):=by positivity
 unfold can; exact ⟨r,(div_le_iff₀ hr).mpr (le_of_le_of_eq ((div_le_iff₀ p).1 ht) (mul_comm ..))⟩
-- dyadic option
lemma dyr (e:ℝ)(p:0<e): ∀ᶠ k:ℕ in atTop,can e (2^k):=by
 obtain ⟨r,hr⟩:=buyX e p; filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1<(2:ℕ))).eventually_ge_atTop r.val] with k hk; apply le_trans _ hr; have hx:=X_pay.le; apply div_le_div_of_nonneg_left hx (by positivity); apply Nat.cast_le.mpr; simpa using hk

def prie(r:Side):ℝ:= 1/r.val
def tip(r:Side):ℝ:= prie r / (4*r.val*xm)
lemma tip_pos(r:Side) : 0<tip r:=by have he:=xm_p; unfold tip prie; positivity
lemma tip_license (r:Side)(k:ℝ)(h:0≤k)(e:k≤tip r): XF.cap r k:=by
 have he:=xm_p; have hr:0<(r.val:ℝ):=by positivity
 refine ⟨h,?_⟩; unfold tip at e; rw [le_div_iff₀ (by positivity)] at e; exact le_trans (by push_cast; change xm*_ ≤ _; exact le_of_eq (by ring)) e -- tune placeholder.

-- native.
def EdgePrice (X:Site s→Ballot)(U:Bkg s)(b:Bond s):ℝ:= ‖turn (U b) (X (b.1+step b.2)).val-(X b.1).val‖
def PaceX (S:Set (Site s))(U:Bkg s)(F:Site s→Ballot)(d:ℝ): Prop:= ∀ x i,x∈S→ x+step i∈S→ EdgePrice F U (x,i)≤d
def SkinH (S:Set (Site s))(U:Bkg s)(F:Site s→Stamp)(d:ℝ): Prop:= ∀ x i,x∈ S → x+step i∈S → ‖motion (U (x,i)) (F (x+step i))-F x‖≤d
lemma slide4 (x:Site s)(i:Axis): Grid.slide x i=x+step i:=by ext j; by_cases h:j=i <;> simp [Grid.slide,h] -- tune
lemma Way (x y:Site s) : Grid.dist x y=separation x y:=rfl
abbrev Lawr (U:Bkg s):= U -- maybe remove
lemma price_slide (x:Site s)(i:Axis)(U:Bkg s)(V:Site s→Ballot):XF.costW V U x i=EdgePrice V U (x,i):=by rw [Grid.Fiber.costW,slide4]; apply norm_sub_rev
lemma grid_pace (U:Bkg s)(V:Site s→Ballot)(p:Grid.Entity 4 c)(d:ℝ) : XF.Fast g V U p d ↔ PaceX {x| p.Mem g x} U V d:=by unfold Grid.Fiber.Fast PaceX; simp_rw [price_slide,slide4]; rfl
lemma EdgePrice_move(X:Site s→Ballot)(U:Bkg s)(b:Bond s)(g:Site s→ E): EdgePrice (fun x=>scaledV (g x) (X x)) (gauge g U) b= EdgePrice X U b:=by
 obtain ⟨x,i⟩:=b; let L:=g (x+step i); unfold EdgePrice Lattice.gauge; dsimp only; unfold scaledV; dsimp only; rw [← turn_seq, inv_mul_cancel_right, turn_seq, ←turn_sub,turn_norm]
lemma pace_sub (X:Site s→Ballot)(U:Bkg s){A B:Set (Site s)}{a b:ℝ}(h:PaceX A U X a)(e:B⊆A)(t:a≤b) : PaceX B U X b:=fun x i hx ht=>(h x i (e hx) (e ht)).trans t
lemma pace_move (X:Site s→Ballot)(U:Bkg s){A:Set (Site s)}{a:ℝ}(g:Site s→ E): PaceX A (gauge g U) (fun x=> scaledV (g x) (X x)) a ↔ PaceX A U X a:=by unfold PaceX; simp only [EdgePrice_move]
lemma skin_sub (X:Site s→Stamp)(U:Bkg s){A B:Set (Site s)}{a b:ℝ}(h:SkinH A U X a)(e:B⊆A)(t:a≤b):SkinH B U X b:=fun x i hx ht=>(h x i (e hx) (e ht)).trans t
lemma pace_slow{X:Site s→Ballot}{U:Bkg s}{a b:ℝ}(h:PaceX Set.univ U X a)(u:a<b): Slow U (fun x=> (X x).val) b:= fun x i=>(h x i trivial trivial).trans_lt u

-- Grid.enter API
variable (P : Set (Grid.Entity 4 c))(A: Site s→Ballot)(U:Bkg s)(d:ℝ)
def expandX := XF.enter g P (U,A) 4
lemma enter_here(x:Site s)(p:Grid.Entity.chief g x∈P): expandX g P A U x=A x:= XF.fix_old _ _ _ _ _ p
lemma entersX (e: can d g.count)(W : Set (Grid.Entity 4 c))(p:4≤c.val)(s:Grid.Settle P)(t:Grid.Settle W)
 (X:∀ q∈P,PaceX {x | q.Mem g x} U A (prie g.count))(Y:∀ q∈W,Grid.Fiber.okay g U (tip g.count) q): ∀ q∈W, PaceX {x|q.Mem g x} U (expandX g P A U) d:=fun q hx=> (grid_pace g _ _ _ _).1 ((XF.stroll g P (U,A) W p s t (fun l m=>(grid_pace g _ _ _ _).2 (X l m)) (tip_license _ _ (tip_pos _).le le_rfl) Y 4 q hx (by have ht:= Finset.card_le_univ q.axes; rw [Fintype.card_fin] at ht; exact ht)).mono e) -- tune
lemma expandX_m : Measurable (fun x:Bkg s × (Site s→ Ballot)=> expandX g P x.2 x.1):= XF.enter_c ..
lemma expandX_eq (h:Grid.Entity 4 c)(e:4≤c.val)(V:Set (Grid.Entity 4 c))(t:∀ q,q.Under h→ (q∈P ↔ q∈V)) (Y:Site s →Ballot)(B:Bkg s)(p:Set.EqOn A Y {x|h.Mem g x})(u:Lattice.Agrees {x|h.Mem g x} U B) : Set.EqOn (expandX g P A U) (expandX g V Y B) {x|h.Mem g x}:=by
 refine XF.enter_eq g P h e t (fun i hi=> u i hi.1 ?_) p 4; rw [←slide4]; exact hi.2
end YM.CF.BProof.Hero
