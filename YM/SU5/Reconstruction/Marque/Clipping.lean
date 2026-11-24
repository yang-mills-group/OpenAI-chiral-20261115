import YM.SU5.Reconstruction.Marque.Ticket
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
variable {N S Ω X Y Z}
local notation "G"=> Z.mirror
namespace Annual
variable (p:Annual N S Ω X Y Z)
local notation "P"=> Projector N S Ω
local notation "U'"=>Driver (S:=S) (Z:=Z)
noncomputable def Kin(g:Two): Wander H.space:= if e:Blank g then Classical.choose (p.issues g e) else 1
include p
local notation "J"=> Kin p
lemma Here(g:Two)(e:Blank g): U' g (J g):= by rw [Kin,dif_pos e]; exact (p.issues g e).choose_spec
lemma atB:J Basin=G:= p.consistency _ _ (p.Here Basin basin_price) ⟨1,1,(P).pass,Or.inl (by unfold rehome;simp), (by unfold rehome;simp)⟩
lemma Powered(g:Two)(e:Blank g):News (Ω:=Ω) N S true g (J g):= by
 obtain ⟨u,v,q,a,b⟩:= p.Here g e
 have ht: News (Ω:=Ω) N S false u v:= (permit ..).1 q
 have hk:ℵ true (rehome u Basin) (J g):= b ▸ ((ht.compose p.window).compose ht.inverse)
 rcases wrap_case _ a with a|a; exact a ▸ hk
 have hy:ℵ true (bezel* (bezel*g)) (1*J g):= News.bez.compose (a ▸ hk); simpa only [←mul_assoc,bezel_sq,one_mul] using hy
lemma seals : (ℶ).Paddles J:= by
 constructor; exact p.centre; exact p.upright
 · intro g t e v; have hk:= p.Here t (lipSign g e v); apply p.consistency g _ (p.Here _ e)
   obtain ⟨s,i,p1,p2,b⟩:=hk; refine ⟨s,i,p1,?_,b⟩; rcases wrap_case _ v with v|v <;> rw[v] at p2; exact p2; rwa [wrap_bezel] at p2
 · intro g e; obtain ⟨_,u,_,_,b⟩:=p.Here g e; rw [b,← rehome_mul,Z.well]; unfold rehome;group
 · exact fun s t e v=>(permit N S Ω (s*t) (J s * J t)).2 ((p.Powered s e).compose (p.Powered t v))
 intro g s v e q; obtain ⟨a,u,b,t,h⟩:= p.Here s q; apply p.consistency (rehome g s) (J (rehome g s)) (p.Here _ (by unfold Blank;simp[q]))
 refine ⟨g*a,v*u,(ℶ).plus e b,?_,?_⟩; rw [rehome_comp]; exact wrap_acts s g t -- tune
 rw [rehome_comp,h]
noncomputable def banner:= p.seals.Pennant
local notation "ℶ₁"=> banner p
lemma allWalk(g:Two): Lot N S Ω false g (ℶ₁ g):= ((permit ..).1 (p.seals.answer g)).toLot
lemma payBezel:ℶ₁ bezel=1:=p.seals.double
lemma pennantX(t:ℝ) : ℶ₁ (Zip t)=X.boost (2*t):=by
 rw [← show ℶ₁ (bezel*Zip t)=ℶ₁ (Zip t) from (by rw [map_mul,p.payBezel,one_mul]), show bezel* Zip t=rehome (Zip (t/2)) Basin*Basin from (blankOut ..).symm];
 change Paddles.Victory J _=_; rw [p.seals.swipe _ Basin (show lip _=0 from by rw [lip_invariant]; exact basin_price) basin_price, p.seals.mirrors _ _ (X.boost (2*(t/2))) (p.newsX _) basin_price,p.atB,show 2*(t/2)=t by ring]
 let x:=p.Wz; have ht:Conveys G (A 0) (A 0):= by
    have e:= x.ready (Λ 0) (openWedge clock 0); rwa [allImage (roller true Basin).surjective (Λ 0) (Λ 0) (fun i=>(show _ from (by rw [away,← basinMotion]; exact (lo (by decide:clock≠(2:Axis)) (by decide:(2:Axis)≠0) (by decide:clock≠(0:Axis)) i).symm)))] at e -- universe
 have hp:G*(X.boost t)⁻¹=X.boost t * G:= by
    rw [← X.flip]; conv_rhs=> arg 1; rw [show t=beamRate true (-t) from (by simp[beamRate])]
    exact X.locksFlight X _ Z.confirm Z.cool ht
 unfold rehome; rw [mul_assoc (X.boost t) G ((X.boost t)⁻¹),hp,←mul_assoc,← X.rise,mul_assoc,Z.well,mul_one]; congr 1; ring
lemma pennantY(t:ℝ) : ℶ₁ (Yell t)=Y.boost (2*t):=by
 rw [← show ℶ₁ (bezel*Yell t)=ℶ₁ (Yell t) from (by rw [map_mul,p.payBezel,one_mul]), show bezel* Yell t=rehome (Yell (t/2)) Basin*Basin from (blankOut ..).symm];
 change Paddles.Victory J _=_; rw [p.seals.swipe _ Basin (show lip _=0 from by rw [lip_invariant]; exact basin_price) basin_price, p.seals.mirrors _ _ (Y.boost (2*(t/2))) (p.newsY _) basin_price,p.atB,show 2*(t/2)=t by ring]
 let x:=p.Wz; have ht:Conveys G (A 1) (A 1):= by
    have e:= x.ready (Λ 1) (openWedge clock 1); rwa [allImage (roller true Basin).surjective (Λ 1) (Λ 1) (fun i=>(show _ from (by rw [away,← basinMotion]; exact (lo (by decide:clock≠(2:Axis)) (by decide:(2:Axis)≠1) (by decide:clock≠(1:Axis)) i).symm)))] at e -- universe
 have hp:G*(Y.boost t)⁻¹=Y.boost t * G:= by
    rw [← Y.flip]; conv_rhs=> arg 1; rw [show t=beamRate true (-t) from (by simp[beamRate])]
    exact Y.locksFlight Y _ Z.confirm Z.cool ht
 unfold rehome; rw [mul_assoc (Y.boost t) G ((Y.boost t)⁻¹),hp,←mul_assoc,← Y.rise,mul_assoc,Z.well,mul_one]; congr 1; ring
lemma pennantZ(t:ℝ): ℶ₁ (Tuning t)=Z.boost (2*t):= by
 obtain ⟨i,r⟩:=p.upright.always Nine; have hp: Φ false Nine i := ((permit ..).1 r).toLot
 have e:Conveys i (A 0) (A 2):= by
    have ht:= hp.ready (Λ 0) (openWedge clock 0); rwa [allImage (roller false Nine).surjective (Λ 0) (Λ 2) (fun x => wing_turn x)] at ht
 rw [←turn_rail]; rw [show ℶ₁ _=rehome i (ℶ₁ (Zip t)) from p.seals.rotate _ Nine i r,p.pennantX, rehome, X.locksFlight Z (2*t) hp.fleet hp.pecan e]; unfold beamRate; simp
lemma schedule: Continues ℶ₁:= by
 apply Paddles.arches; -- uses Vr private circumvent explicit p
 · intro v; change Continuous (fun t:ℝ=> (ℶ₁) (Tuning t) v); simp_rw [p.pennantZ]; exact (Z.orbit v).comp (show Continuous (fun v:ℝ=>2*v) by fun_prop)
 · intro v; change Continuous (fun t:ℝ=> (ℶ₁) (Zip t) v); simp_rw [p.pennantX]; exact (X.orbit v).comp (show Continuous (fun v:ℝ=>2*v) by fun_prop)
 intro v; change Continuous (fun t:ℝ=> (ℶ₁) (Yell t) v); simp_rw[p.pennantY]; exact (Y.orbit v).comp (show Continuous (fun v:ℝ=>2*v) by fun_prop)
end Annual
end YM.Marque.Flow
