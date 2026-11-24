import YM.SU5.FiniteGaugeData.KernelP.Club
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
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
-- buy a window in the character measure with ALL profile tests approximated
variable (p:Actors Y h a W' R (A a))(α:p.val.X)(C ε:ℝ)
local notation "F"=> Camera Y h a W' R (A a)
local notation "B"=> KeySet Y h a W' R (A a)
local notation "m"=> p.val.μ
local notation "μ"=> p.val.X -- clashes
local notation "X" s:max=> Hills.route Y h s a W' R (A a)
local notation "σ" s:max=> issueH Y h s a W' R (A a) p α
include p α
private lemma vote_price (x y:Charm.W (tent Y h)): ‖issueH Y h s a W' R (A a) p α x -issueH Y h s a W' R (A a) p α y‖ ≤ dist (Hills.route Y h s a W' R (A a) x) (Hills.route Y h s a W' R (A a) y):=by
 rw [dist_eq_norm,← map_sub (f:=(σ s)), ←map_sub (f:=(X s))]; exact vote_box .. -- séance f infer
section
omit p α
private lemma fare_phi {H:Hilbert}(x y:H.Op)(t:H)(p:‖t‖=1):dist (inner ℂ t (x t)) (inner ℂ t (y t))≤ dist x y:= by
 rw [dist_eq_norm x y,dist_eq_norm,←inner_sub_right,← _root_.sub_apply]; exact (norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left ((x-y).le_opNorm t) (norm_nonneg _)).trans_eq (by rw [p,one_mul,mul_one]))
lemma close_frame {H:Hilbert}(U:H.Op)(x y:H)(p:‖y‖=1)(d r C:ℝ)(b:‖x‖ ≤ d)(h: ‖x-y‖≤ r)(z:‖U‖≤ C): dist (inner ℂ x (U x)) (inner ℂ y (U y)) ≤ (1+d)*C*r:= by
 have hz:0≤ C:= le_trans (norm_nonneg _) z; have hc:0≤ r:= le_trans (norm_nonneg _) h
 have he:dist (inner ℂ x (U x)) (inner ℂ x (U y)) ≤ d*C*r:= by
    rw [dist_eq_norm,←inner_sub_right,←map_sub]; exact (norm_inner_le_norm ..).trans (le_trans (mul_le_mul b ((U.le_opNorm _).trans (mul_le_mul z h (norm_nonneg _) hz)) (norm_nonneg _) ((norm_nonneg x).trans b)) (mul_assoc ..).symm.le)
 have hp:dist (inner ℂ x (U y)) (inner ℂ y (U y)) ≤ r*C:= by rw [dist_eq_norm,←inner_sub_left]; refine (norm_inner_le_norm ..).trans (mul_le_mul h ?_ (norm_nonneg _) hc); exact (U.le_opNorm _).trans (by rwa [p,mul_one])
 exact (dist_triangle _ (inner ℂ x (U y)) _).trans (le_trans (add_le_add he hp) (le_of_eq (by ring)))
end
lemma tableau (b:0<ε) :∃ x:Camera Y h a W' R (A a), ‖x‖=1∧ ∀ (f:W (tent Y h))(e:Locator Kₜ f S),‖reading Kₜ S f e‖≤ C→ dist (inner ℂ x (Hills.route Y h s a W' R (A a) f x)) (issueH Y h s a W' R (A a) p α f)≤ ε:= by
 classical
 let U:=Lobby Y h S C; let V(i:U):= Hills.route Y h s a W' R (A a) i.val
 have hx:= (view_compact Y h S s a W' R (A a) C (fun i:U=>i.val) (fun i=>Classical.choose i.property) (fun i=> Classical.choose_spec i.property)).totallyBounded
 have he:0<ε/3:=by positivity
 obtain ⟨T₀,fp,t⟩:= Hierarchy.equip (t:=ε/3) he V (hx.subset subset_closure)
 let P(i:U):= readingH Y h s a W' R (A a) i.val; obtain ⟨x,p',u⟩:= coneB p.property α (ε/3) he (fp.toFinset.image P) (faith Y h a W' R (A a));
 refine ⟨x,p',fun w c e=>?_⟩; let y:U:=⟨w,c,e⟩; obtain ⟨l,q,v⟩:=t y; let f(k:U):= inner ℂ x (V k x); let g(k:U):=(σ s) k.val; have ht: dist (f y) (f l)≤ ε/3:=(fare_phi (V y) (V l) x p').trans v.le; have hb: dist (g l) (g y)≤ ε/3:=by rw [dist_comm,dist_eq_norm]; exact (vote_price Y h s W' R A a p α _ _).trans v.le;
 have hv: dist (f l) (g l) ≤ ε/3:= by rw [dist_eq_norm]; exact u (P l) (mem_image_of_mem P (fp.mem_toFinset.2 q))
 exact (dist_triangle4 (f y) (f l) (g l) (g y)).trans (by linarith) -- order

variable (e:Studio a 0 (yard (tent Y h) d) (reserve Λ l) S)(q:0<d)
local notation "Ω"=> (A a).space
local notation "W0" i:max=> store Y h i W' R a (A a)
local notation "U"=> (StructureH Y h a W' R (A a)).Unity
include e q
lemma approximation (z:0≤C)(h':0<ε):∃ (x:(A a).space)(y:(A a).space), y∈ (U)∧ ‖y‖=1∧∃ (n:ℕ) (f:Decko Y h a), store Y h (s+n) W' R a (A a) f=x ∧ dist x y≤ ε ∧
    ∀ (v:W (tent Y h))(t:Locator Kₜ v S),‖reading Kₜ S v t‖≤ C→ dist (inner ℂ x (Wedge Y h s a d W' R (A a) (f:=v) ⟨S,e,t⟩ q x)) ((σ s) v) ≤ ε:=by
 obtain ⟨w,g,t⟩:=tableau Y h S s W' R A a p α C (ε/2) (by positivity)
 let Z:=venus Y h S s a d; have hZ:0<Z:= Real.exp_pos _; let B':= C*duration S/Z; let y:=cpo (U) w; have hp':0≤ B':= div_nonneg (mul_nonneg z (duration_pos _).le) hZ.le; have hy:‖y‖=1:=(Hills.yen ..).trans g; let V:=(1+(1+ε))*(B'+1); have hV:0<V:= by unfold V; positivity
 let u:= min ε ((ε/2)/V); have hu:0<u:= by unfold u; positivity
 obtain ⟨x,⟨v',rfl⟩,d'⟩:= Metric.mem_closure_iff.mp ((A a).issued y) u hu; let x:=(A a).paid v'; have hx:‖x-y‖ ≤ u:=(by rw [← dist_eq_norm,dist_comm]; exact d'.le); have hv:dist x y≤ ε:=by rw [dist_eq_norm]; exact hx.trans (min_le_left ..)
 obtain ⟨n,t₀,v⟩:= ((eventual_table Y h W' R a (A a) v').and (eventually_ge_atTop s)).exists; obtain ⟨n,rfl⟩:= Nat.exists_eq_add_of_le v
 refine ⟨x,y,among («U»:= (U)) w,hy,n,_, t₀,hv,fun f c w'=>?_⟩
 let p':Plan Y h a d f:=⟨S,e,c⟩; let F' := Wedge Y h s a d W' R (A a) p' q; have hb':‖F'‖≤ B'+1:= le_trans ((wedge_lip Y h S s a d W' R (A a) p' q c).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right w' (duration_pos _).le) hZ.le)) (by linarith : B'≤B'+1)
 have hz: inner ℂ y (F' y) = inner ℂ w ((X s) f w):=by rw [route_formula Y h s a d W' R (A a) p' q,sightS]
 have he:‖x‖≤1+ε:=by have he:= norm_le_norm_sub_add x y; rw [hy] at he; rw [dist_eq_norm] at hv; linarith
 have hF:=close_frame (H:=(A a).space) F' x y hy (1+ε) ((ε/2)/V) (B'+1) he (hx.trans (min_le_right ..)) hb'; refine le_trans (dist_triangle (inner ℂ x (F' x)) (inner ℂ y (F' y)) ((σ s) f)) (le_trans (add_le_add (le_trans hF ?_) (hz.symm ▸ (t f c w'))) (add_halves ε).le); exact (show V*(ε/2/V)≤ ε/2 by rw [mul_comm V,div_mul_cancel₀ _ hV.ne'])
#print axioms approximation
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
