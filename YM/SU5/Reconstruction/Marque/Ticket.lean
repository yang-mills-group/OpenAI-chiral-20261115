import YM.SU5.Reconstruction.Marque.Seat
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Metric NormedSpace ContinuousLinearMap BridgeClub CrossedFrame Passage
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical
variable {H:Hilbert}(N:Set E4→Net H)(S:OS.Semigroup H clock)(Ω:H)
local notation "W"=> Wander H.space
local notation "Λ" ζ:max=> Wedge clock ζ
local notation "A" ζ:max=> N (Λ ζ)
local notation "U" => Picket.trans S
local notation "Φ"=> Lot N S Ω
local notation "ℵ"=> News (Ω:=Ω) N S
local notation "ℶ"=> Projector N S Ω
variable (X:Chair N Ω 0)(Y:Chair N Ω 1)(Z:Chair N Ω 2)
structure Annual :Prop where
   Wz: Lot N S Ω true Basin Z.mirror
   px(t:ℝ): Lot N S Ω false (Zip t) (X.boost (2*t))
   py(t:ℝ): Lot N S Ω false (Yell t) (Y.boost (2*t))
   pz(t:ℝ): Lot N S Ω false (Tuning t) (Z.boost (2*t))
variable {N S Ω X Y Z}
local notation "G"=> Z.mirror
namespace Annual
variable (p:Annual N S Ω X Y Z)
local notation "P"=> Projector N S Ω
include p
lemma window : ℵ true Basin G:= ⟨p.Wz,Z.KernelMirror S⟩
lemma news (t:ℝ): (Z.boost (2*t))∈(ℶ).ok (Tuning t):=(permit _ _ _ _ _).2 ⟨p.pz _,Z.KernelBoost S _⟩ -- order?
lemma newsX(t:ℝ): X.boost (2*t) ∈ (P).ok (Zip t):= (permit _ _ _ _ _).2 ⟨p.px _, X.KernelBoost S _⟩
lemma newsY(t:ℝ): Y.boost (2*t) ∈ (P).ok (Yell t):= (permit _ _ _ _ _).2 ⟨p.py _, Y.KernelBoost S _⟩
lemma upright : Upright ℶ:=⟨⟨_,fun v=>(Z.orbit v).comp (show Continuous (fun v:ℝ=>2*v) by fun_prop),fun i=>p.news i⟩,⟨_,fun v=>(X.orbit v).comp (show Continuous (fun v:ℝ=>2*v) by fun_prop),fun i=>p.newsX i⟩,⟨_,fun v=>(Y.orbit v).comp (show Continuous (fun v:ℝ=>2*v) by fun_prop),fun i=>p.newsY i⟩⟩
lemma guard (x:W)(g:Two)(e: rehome g Basin=Basin)(u:Φ false g x) : Conveys x (A 2) (A 2):= by
 obtain ⟨t,rfl⟩:= sameBasin g e; have h:= u.ready (Λ 2) (openWedge clock 2); rw [allImage (Y:=E4) (f:=roller false (Pole t)) (roller ..).surjective (Λ 2) (Λ 2) (basis_motion t)] at h; exact h
lemma centre : Centre ℶ:= by
 refine ⟨allSpokes N S Ω,fun t w u v f e=>?_,(permit N S Ω bezel 1).2 News.bez⟩;
 have hv:(Z.boost (2*t))∈(ℶ).ok (Tuning t):=p.news _
 replace e:= (permit N S Ω (Pole w) v).1 e
 have hp: rehome (Pole w) Basin=Basin:= by unfold Basin rehome; rw[(Pole_comm w Sugar).eq]; group
 have hk:v*Z.boost (2*t)=Z.boost (beamRate false (2*t))*v:= Z.locksFlight Z (2*t) e.fleet e.pecan (p.guard v (Pole w) hp e.toLot) -- rate reducible
 have hy: Commute (u*(Z.boost (2*t))⁻¹) v:= e.vert (u* _) (((permit N S Ω 1 _).1 (by simpa only [mul_inv_cancel] using (ℶ).plus f ((ℶ).opp hv))).toLot)
 nth_rw 1 [show u=(u*(Z.boost (2*t))⁻¹)* (Z.boost (2*t)) from (by group)]
 exact hy.mul_left hk.symm
lemma pMirror:Conveys G (N (Λ 2)) (N (Counter clock 2)):=by
 have hx:=p.Wz.ready (Λ 2) (openWedge clock 2); rw [allImage (roller true Basin).surjective (Λ 2) (Counter clock 2) (f:=roller true Basin) (fun i=>(show _ from (by rw [away,← basinMotion]; exact (turning ..).symm)))] at hx; exact hx
lemma knows (g:Two)(e:rehome g Basin ∈ Wrap Basin)(u:W)(z:Lot N S Ω false g u) : Commute u G:= by
 rcases wrap_case _ e with e|e; exact Z.looksCred Z z.fleet z.pecan (p.guard u g e z)
 obtain ⟨v,h⟩:= oppositeBasin g e; subst g
 have ht:= z.ready (Λ 2) (openWedge clock 2)
 have he: Conveys u (A 2) (N (Counter clock 2)):= by
       rw [allImage (roller false (YM.Marque.turn*Pole v)).surjective (Λ 2) (Counter clock 2) (f:= roller false _) (fun x=>?_)] at ht; exact ht
       rw[forwards,multiplies]; exact (basis_motion v x).trans (turnMotion _)
 have hb:= p.pMirror.back; rw[Z.often] at hb
 have hx:= Z.looksCred Z (z.fleet.times (p.Wz.fleet)) (show (G*u) Ω=Ω from (by rw [wander_mul,z.pecan,Z.cool])) (he.joins hb z.fleet)
 change u*G = G*u
 calc u*G = G*(G*u*G) := by rw [← mul_assoc G (G*u), ←mul_assoc G G,Z.well,one_mul]
      _ = _ := by rw [hx,←mul_assoc,Z.well,one_mul]
-- paddle construction using transport
variable (v u:Two) (t:Wander H.space)
omit p
noncomputable def Driver (q:Two)(f:W):Prop:=∃ (g:Two)(u:W),u∈ (P).ok g ∧ rehome g Basin ∈ Wrap q ∧ f=rehome u G
-- uses N S Ω Z
include p
lemma issues (p':Blank u):∃ x,Driver (S:=S) (Z:=Z) u x:=by
 obtain ⟨g,e⟩:=blankChart u p'; obtain ⟨x,v⟩:=p.upright.always g; exact ⟨_,g,x,v,Or.inl e,rfl⟩
lemma consistency (a:Driver (S:=S) (Z:=Z) v t) {u:W}(q:Driver (S:=S) (Z:=Z) v u): t=u:=by
 obtain ⟨g,u',b,c,rfl⟩:=a; obtain ⟨d,w,h,j,rfl⟩:=q; have e: rehome (d⁻¹*g) Basin∈ Wrap Basin:= by
    have x:rehome g Basin∈Wrap (rehome d Basin):= by rcases wrap_case _ j with j|j; rw[j];exact c; rw[j,wrap_bezel];exact c
    rw [rehome_comp]; simpa only [rehome_back] using wrap_acts (u:=d⁻¹) _ x
 have u:= p.knows _ e _ ((permit ..).1 ((ℶ).plus ((ℶ).opp h) b)).toLot
 unfold rehome; have v:u' * G = w * G * w⁻¹ * u':= by
      rw[mul_assoc w G w⁻¹]; -- convert using u
      calc _=w*((w⁻¹*u')*G) := by group
           _=_:= by rw [u.eq];group
 rw [v]; group
end Annual
end YM.Marque.Flow
