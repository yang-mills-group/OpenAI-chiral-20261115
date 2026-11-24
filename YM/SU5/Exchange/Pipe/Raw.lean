import YM.SU5.Exchange.Pipe.Latch
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial
open Kennel
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{k:ℕ}
local notation "Ω"=> Single N
variable {P K:SOp N}(p:Solo a b P d)(t:Solo a b K d)(u:0 ≤ a)
-- actual O countermarch cells, exponential bill
abbrev sunA(P K:SOp N)(V:Chin N):= capT (P V) (K V)
abbrev feeRise(a b:ℝ):= 2*((2*((Real.exp a+b)*b))*b)
include p t u
lemma fee_Ξ:Solo a (feeRise a b) (sunA P K) d:=by
 let H: Solo a (Real.exp a) (fun _:Chin N =>(1:Op Ω)) d:= Crown.ident ..; exact (((H.sub p).product t u).product p u)
abbrev payΩ (a b w:ℝ):= (2*((2*(b*w))*b))+(2*((2*((Real.exp a+b)*w))*(Real.exp a+b)))
lemma blockE (W:Op Ω)(w:Soak o (fun _=>W) a v d):Soak o (fun x=>blockD (P x) W) a (payΩ a b v) d:=by
 let H: Solo a (Real.exp a) (fun _:Chin N=>(1:Op Ω)) d:= Crown.ident ..; let z:=H.sub p; exact plus_U (aura_X (aura_Y w p u) p u) (aura_X (aura_Y w z u) z u)
abbrev inlandW(a b:ℝ):=oneMill a+2*((2*((Real.exp a+feeRise a b)*payΩ a b (oneMill a)))*(Real.exp a+feeRise a b))
lemma inlandFee (x:Site N): Soak (node x) (millIntro P K x) a (inlandW a b) d:=by
 let H: Solo a (Real.exp a) (fun _:Chin N =>(1:Op Ω)) d:= Crown.ident ..; let Z:=fee_Ξ p t u; let W:= millBill (d:=d) (a:=a) x; apply minus_Q W (aura_X (aura_Y (blockE p t u _ W) (H.plus Z) u) (H.sub Z) u) -- order
omit p t u
lemma inwardE (f:Staffer P K d)(V:Pane N)(g:Guard V d)(x:Site N)(m:ℕ) : inward (P (profile V)) (windmill x m) (K (profile V))= ∑ i:Axis, (spur (millIntro P K) (x+m • step i) i m (profile V)-spur (millIntro P K) (x-m • step i) i m (profile V)):=by
 have hx: (∑ x:Site N,millIntro P K x (profile V))=0:= inwardFlux _ millQ _ _ (f.projection _ g) sumCell
 let F:= millIntro P K; let U:= P (profile V); let D:=K (profile V); let A:Op Ω→+ Op Ω:=⟨⟨fun i=> inward U i D,by simp [inward,blockD]⟩,fun x y=> by unfold inward blockD; simp only [mul_add,add_mul]; abel⟩ -- tune
 let l:=List.ofFn (id:Axis→Axis)
 rw [show inward _ _ _= _ from squareMap A millQ m l x]; exact millEquation _ _ hx _ _
abbrev co_Ψ (t u: Site N)(X:SOp N): SOp N:=julStep (taxiPlus (t-u)) X
lemma co_Ξ (t u: Site N) (x:X=X)(h:Soak (node u) X a b d): Soak (node t) (co_Ψ t u X) a (Tenant.quota^2*b) d:= by rw [show node t=boxA (taxiPlus (t-u)) (node u) from (by rw [platforms, add_sub_cancel])]; exact jul_sells _ h -- t remains in Ψ after rw depends t? rw all node t

structure CrownCar {N:Side} (P K:SOp N) (o:Site N) (k m:ℕ) (b a Z:ℝ) :Prop where
  tickets : ∃ (J T:Axis→SOp N) (X Y:SOp N), (∀ l, Trunk (node o) (J l) k b Z a) ∧ (∀ l,Soak (node o) (T l) b (Real.exp (-b*k)*Z) a) ∧ Trunk (node o) X k b Z a ∧ Soak (node o) Y b (Real.exp (-b*k)*Z) a ∧
    (∀ (l:Axis)(z:Openc (More N) a),spur (millIntro P K) o l m z.val=J l z.val+T l z.val)∧∀ z:Openc (More N) a, (P z.val-Dial.tickA N)*windmill o m=X z.val+Y z.val
open Dial
lemma millTester (p:Solo a b P d)(h:0≤a)(x:Site N)(m:ℕ):Soak (node x) (fun V=> (P V-tickA N)*windmill x m) a (2*((b+ Tap.wingRent Fir.Aop a)*((stripW a m)^4*oneMill a))) d:=by
 have hz:= aura_Y (windmillCost (d:=d) x m h) (show Solo a (b+Tap.wingRent Fir.Aop a) (fun v:Chin N=>P v-tickA N) d from p.sub (Tap.soil_tick a d)) h; simpa only [List.length_ofFn] using hz
lemma crownsLearnt (b a d:ℝ)(hb:0<b)(ha:0<a)(m:ℕ):∃ B> (0:ℝ),∀ {N:Side}(k:ℕ)(P K:SOp N), Solo (100*(a+a)) b P d→ Solo (100*(a+a)) b K d →∀ (o:Site N), CrownCar P K o k m a d B:=by
 have hu:0 ≤ 100*(a+a):=by positivity
 have hp:0≤ inlandW (100*(a+a)) b:=by unfold inlandW feeRise payΩ oneMill; positivity
 obtain ⟨U,H,v⟩:= spurSells (d:=d) m (show 0<a+a from add_pos ha ha) hp
 let Z:= 2*((b+ Tap.wingRent Fir.Aop (a+a))*((stripW (a+a) m)^4*oneMill (a+a)))
 let W:= max Z U; refine ⟨W,H.trans_le (le_max_right ..),?_⟩; intro N k P K P0 K0 o
 have hG(i:Axis):=cut_tr k (lift_U (v (millIntro P K) (fun i=>inlandFee P0 K0 hu i) o i) (show U≤ W from le_max_right ..)) ha
 choose J T P₀ P₁ p_ using hG
 obtain ⟨X,Y,p,q,g⟩:= cut_tr k (lift_U (millTester (P0.drop (by linarith:a+a ≤ 100*(a+a))) (add_nonneg ha.le ha.le) o m) (show Z≤ W from le_max_left ..)) ha
 exact ⟨J,T,X,Y,P₀,P₁,p,q,p_,g⟩

-- orientation equality, at every guard profile even with noncanonical extension. no equality asserted outside.
lemma co_Set (u x:Site N)(A T:SOp N)(p:Staffer P K d)(a:Axis)(k:ℕ) (H:∀ z:Openc (More N) d,spur (millIntro P K) u a k z.val=A z.val+T z.val)(v:0<d)(V:Pane N) (h:Guard V d): spur (millIntro P K) x a k (profile V)= co_Ψ x u A (profile V)+ co_Ψ x u T (profile V):=by
 let t:=x-u; let s:=taxiPlus t; let U:=flashA s V; let Z:=γS s; have hv:Guard U d:=keepC (xtra s.charge) (castX s) V d h
 let z: Openc (More N) d:=⟨profile U,U,hv,by simpa⟩
 have hp:= limb (P:=P) V t p u a h k; have he: u+t=x:= by unfold t; abel
 rw [he] at hp
 apply (twist Z).injective; rw [map_add]; rw [show (twist Z).toRingEquiv (spur (millIntro P K) x a k (profile V))=_ from hp, show (twist Z).toRingEquiv (co_Ψ x u A (profile V))=_ from julius s A V,show (twist Z).toRingEquiv (co_Ψ x u T (profile V))=_ from julius s T V] -- rw motive uses windX pattern
 exact H z
end YM.CF.Swell
