import YM.SU5.FiniteGaugeData.Hills.Fathom
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey
namespace Hills
variable (a b:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)(B:Repertory Y h W' R b)(p:a≠b)
local notation "Tz"=> StructureH Y h a W' R A
local notation "Zb"=> StructureH Y h b W' R B
local notation "Va"=> (StructureH Y h a W' R A).Unity
local notation "Vb"=> (StructureH Y h b W' R B).Unity
local notation "F"=> Camera Y h a W' R A
local notation "G"=> Camera Y h b W' R B
local notation "T"=>Pears Y h a b W' R A B
local notation "X" s:max=> route Y h s a W' R A
local notation "X'" s:max=>route Y h s b W' R B
variable {x y:W (tent Y h)}
variable (t:Plan Y h a d x)(q:0<d)
include A q t
-- all time-motive strict.Spectrum.Budget.
lemma energy_h : 0<energyS Λ d n:=by unfold energyS; positivity
lemma met_coherent : Wedge Y h s a d W' R A t q=Wedge Y h (s+n) a (energyS Λ d n) W' R A (Plan.rides Y h s n W' R t) (energy_h Y h a d n W' R A t q):= by
 induction n with
 | zero=> exact equalWick Y h s a d _ _ W' R A t q (Plan.rides Y h s 0 W' R t) _ (by rw [energy_zero]) rfl -- ascending at 0
 | succ n ih=>
    let f:= ascended Y h s W' R n x; let P:= (Plan.rides Y h s n W' R t); let K:= Plan.upgraded Y h (s+n) W' R P; let q':= energy_h Y h a d n W' R A t q
    have he:=wedge_step Y h (s+n) a _ W' R A P q' K (mul_pos Λ.R.L.property q'); exact ih.trans (he.trans (equalWick Y h (s+n+1) a _ _ _ W' R A K _ _ _ (by rw [energy_step]) (by rfl))) -- proof term huge simplify
omit t q A
lemma forestW {H:Hilbert}{U:ClosedSubmodule ℂ H}(s:ℕ)(L:ℕ→ H.Op)(w:H.Op)(g v:H.Op)(p:strong L w): strong (fun i:ℕ=>social U (g*L (s+i)*v)) (social U (g*w*v)):= by
 have he:strong (fun i:ℕ=> L (s+i)) w:= fun x=> (p x).comp ((tendsto_add_atTop_nat s).congr fun i=> add_comm i s)
 exact ((he.follows g).leads v).socializes
include t q A B p
local notation "U"=> Sync (T)
lemma assemblage (T': Plan Y h b d x)(g:Plan Y h a d y)(v₁: Plan Y h b d y): Sync (T) ((X s) x*(X s) y) ((X' s) x*(X' s) y) ∧ Sync (T) ((X s) x*(X s) y) ((X' s) y*(X' s) x):=by
 rw [route_formula Y h s a d W' R A t q,route_formula Y h s a d W' R A g q,route_formula Y h s b d W' R B T' q,route_formula Y h s b d W' R B v₁ q,←social_mul,← social_mul,← social_mul]
 let D:= Wedge Y h s a d W' R A t q; let E₁:= Wedge Y h s a d W' R A g q; let D':= Wedge Y h s b d W' R B T' q; let F':= Wedge Y h s b d W' R B v₁ q
 let c(i:ℕ):=planeP ((Tz).GalleryH i); let c' (i:ℕ):=planeP ((Zb).GalleryH i)
 have he(i:ℕ): U (social (Va) (D*c (s+i)*E₁)) (social (Vb) (D'*c' (s+i)*F')) ∧ U (social (Va) (D*c (s+i)*E₁)) (social (Vb) (F'*c' (s+i)*D')):=by
    unfold D E₁ D' F'; -- move all to s+i.Use equal widths
    rw [met_coherent Y h s a d i W' R A t q, met_coherent Y h s a d i W' R A g q, met_coherent Y h s b d i W' R B T' q, met_coherent Y h s b d i W' R B v₁ q]; exact ⟨happy Y h _ a b _ W' R A B p (Plan.rides Y h s i W' R t) (Plan.rides Y h s i W' R g) _ _ _, reversal Y h _ a b _ W' R A B p (Plan.rides Y h s i W' R t) (Plan.rides Y h s i W' R g) _ _ _⟩
 refine ⟨.horizon (fun i=>(he i).1) (forestW s _ _ _ _ (Tz).retreat) (forestW s _ _ _ _ (Zb).retreat), .horizon (fun i=>(he i).2) (forestW s _ _ _ _ (Tz).retreat) (forestW s _ _ _ _ (Zb).retreat)⟩
omit t q

-- promote.Core.Slopes moving into rooms b then a. width agree by padding.No other shapes
private lemma packages (x:W (tent Y h)): ∃ (d:ℕ) (g:W (tent Y h)),0<d ∧ Plan Y h a d g∧ Plan Y h b d g∧ route Y h s a W' R A x=(X s) g∧ route Y h s b W' R B x=(X' s) g:=by
 obtain ⟨d,e,v,p₀⟩:=house Y h a x; let y:=clockW Kₜ a v x
 obtain ⟨k,t,z,u⟩:= house Y h b y; let g:= clockW Kₜ b z y
 refine ⟨d+k,g,by omega,plan_larger Y h a d _ g (by omega) (plan_walk Y h a b d y _ ?_ p₀), plan_larger Y h b k _ g (by omega) u,?_,?_⟩ -- argument x should be y
 · exact p.symm
 all_goals unfold g y; rw [stayP,stayP]

lemma twistTie (x y:W (tent Y h)): U ((X s) x*(X s) y) ((X' s) x*(X' s) y)∧U ((X s) x*(X s) y) ((X' s) y*(X' s) x):=by
 obtain ⟨d,w,e,x₁,z,g,f⟩:=packages Y h s a b W' R A B p x; obtain ⟨n,v,i,t,r,D,B'⟩:= packages Y h s a b W' R A B p y
 rw [g,D,f,B']; exact assemblage Y h s a b (d+n) W' R A B p (plan_larger Y h a d _ w (by omega) x₁) (by omega) (plan_larger Y h b d _ w (by omega) z) (plan_larger Y h a n _ v (by omega) t) (plan_larger Y h b n _ v (by omega) r)
lemma anchorJ (X0 Y':(Camera Y h a W' R A).Op)(V U':(Camera Y h b W' R B).Op)(t:T X0 V)(p₀:T Y' U'): Sync (T) (X0*Y') (V*U') ∧ Sync (T) (X0*Y') (U'*V):=by
 obtain ⟨d,x,rfl,rfl⟩:=t; obtain ⟨n,y,rfl,rfl⟩:=p₀; rw [← route_any Y h d a n W' R A x,← route_any Y h d b n W' R B x,← route_any Y h n a d W' R A y,← route_any Y h n b d W' R B y,add_comm n d]; exact twistTie (p:=p) ..
lemma sync_mul {x y:(F).Op}{u v:(G).Op}(t:Sync (T) x u)(r:Sync (T) y v) : Sync (T) (x*y) (u*v):= Sync.common (fun _ _ _ _ e g=> (anchorJ Y h a b W' R A B p _ _ _ _ e g).1) t r
lemma sync_flip {x y:(F).Op}{u v:(G).Op}(t:Sync (T) x u)(r:Sync (T) y v) : Sync (T) (x*y) (v*u):= Sync.rare (fun _ _ _ _ e g=> (anchorJ Y h a b W' R A B p _ _ _ _ e g).2) t r
local notation "Ω"=> orbitSeed Y h a W' R A
local notation "φ"=> orbitSeed Y h b W' R B
omit p in
lemma meet_x (x:W (tent Y h)): Sync (T) (route Y h s a W' R A x) (route Y h s b W' R B x):= .joint ⟨s,x,rfl,rfl⟩
omit p in
lemma sync_identity {x:(F).Op}{y:(G).Op} (t:Sync (T) x y): inner ℂ Ω (x Ω)=inner ℂ φ (y φ):= Sync.goldene Ω φ (fun u v ⟨s,f,h₁,h₂⟩=>by rw [h₁,h₂,orbit_value,orbit_value]) t -- rintro
#print axioms sync_identity
#print axioms sync_mul
#print axioms sync_flip
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
