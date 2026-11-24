import YM.SU5.FiniteGaugeData.Lycan.Joy
/-! # WP24c. Country multipoints extends also to coincident *un-centered*, with eventual exact zero gaps. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Stationary
variable {ι:Type*} (F:ι→Grit)
local notation "Μ"=>ι×SU.Slot
section
variable {x:ℕ→ι→Grit}{r:ℕ→ℝ}{O:ι→ι→Gaia}{U D:ι→SpinIdx}{σ:ι→Window.Family}{ε:ℝ}
structure GlobeP (X:ℕ→ι→Grit) (r:ℕ→ℝ)(σ:ι→Window.Family)(U D:ι→SpinIdx)(O:ι→ι→Gaia):Prop where
 basisE:∀ i:ℕ,0<r i
 comes:Tendsto r atTop atTop
 frameE:∀ (i:ℕ)(j:ι),(X i j).σ=σ j ∧ (X i j).u=U j ∧ (X i j).d=D j
 largeE:∀ a b:ι, Tendsto (fun i=>riseX (r i) ((X i b).landing-(X i a).launch)) atTop (𝓝 (O a b))
 joins:∀ a b:ι,O a b=0→(∀ᶠ i:ℕ in atTop,(X i b).landing=(X i a).launch)
lemma beader(A:Grit)(p:A.landing=A.launch)(N:Side)(M:Male): A.stage N M=0:=by
 let f(i:Site N):= μWallet A M.val (mel i); have he(i:Site N): f (Rush.backN i)= -f i:=by
    obtain ⟨w,h⟩:=Rush.dollar i; change mel (Rush.backN i)=_ at h; unfold f μWallet angleK; rw [p,sub_self,h,Fir.mix_period,Fir.mix_neg _ _ M.property]; let a:= mixL 4 M.val (mel i); have hp:zen (-a)= -zen a:=by rw [←neg_one_smul (R:=ℂ) a,zenS,neg_one_smul]
    rw [hp]; simp [mode,a] -- tune
 have ht:(∑ k,f k)= -(∑ k,f k):=by nth_rw 1 [←Equiv.sum_comp (Rush.backN (N:=N)) f]; simp_rw [he,sum_neg_distrib]
 change (∑ k,f k) /_=_; rw [show ∑ k,f k=0 from (by linear_combination ht/2),_root_.zero_div]
lemma beats(A:Grit)(p:A.landing=A.launch): A.finalIncome=0:=by
 let v(i:ℕ):Side:=⟨2*i+2,by omega⟩; let u(i:ℕ):Male:=⟨⟨2*i+1,by omega⟩,i,(by change 2*i+1=_; rfl)⟩
 have he:= A.authorized (N_:=v) (M_:=u) (show Tendsto _ _ _ from StrictMono.tendsto_atTop (strictMono_nat_of_lt_succ (by intro i; change 2*i+1<2*(i+1)+1; omega))) (StrictMono.tendsto_atTop (strictMono_nat_of_lt_succ (by intro i; change 2*i+2<2*(i+1)+2; omega))) (fun i=> ⟨i+1,by change 2*i+2=_; omega⟩); let H:=he.2
 have hv:Tendsto (fun i:ℕ=>A.stage (v i) (u i)) atTop (𝓝 (0:ℂ)):=by simp only [beader A p]; exact tendsto_const_nhds
 exact tendsto_nhds_unique H hv
private lemma flightK(p q v:ℂ) :‖p-v‖ ≤ ‖p-q‖+‖q-v‖:=by simpa [dist_eq_norm] using dist_triangle p q v
variable (ω:GlobeP x r σ U D O)
include ω
lemma realScore(i j:ι): Tendsto (fun a=> earthV (r a)*aroma (x a i) (x a j)) atTop (𝓝 ((pencil (O i j)) (D j) (U i))):= by
 by_cases p:O i j=0; swap; · exact accolade (O i j) p (X:=fun k=> roof (x k i) (x k j)) (ω.largeE i j) (fun v=>(ω.frameE v i).2.1) (fun v=>(ω.frameE v j).2.2) ω.comes ω.basisE
 rw [p,show Onyx.pencil 0=0 by simp [Onyx.pencil],Matrix.zero_apply]; refine tendsto_const_nhds.congr' ?_; filter_upwards [ω.joins i j p] with n t; rw [aroma,beats _ (by exact t),mul_zero] -- tune eventual proof f λ reduced
lemma rehearP(X:List ι): Tendsto (fun i:ℕ=> (earthV (r i))^(X.length)*Prodigy (x i) X) atTop (𝓝 (absoluteP σ U D O X)):=by
 let C (i:ℕ):Μ→Μ→ℂ:= fun a b=> earthV (r i)*Otter aroma (x i) a b; have h:Tendsto (fun i=> Conv (lint σ) (C i) X) atTop (𝓝 (absoluteP σ U D O X)):=by
   refine priceConv (lint σ) X _ _ (fun i j=>?_); unfold C specter Otter; split_ifs; · exact realScore ω i.1 j.1
   simp only [mul_zero]; exact tendsto_const_nhds
 apply h.congr'; apply Eventually.of_forall; intro i; rw [show lint σ=Techn (x i) from funext (fun t=> by change Window.colors _=Window.colors _; rw [(ω.frameE i t).1])]; exact silkCost (Techn (x i)) (earthV (r i)) X (Otter aroma (x i))
variable (h:Real.exp 1≤Λ.x){I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}(K:Universal Y h u v I E)
variable {P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h K R a)
variable (S':RadioCity.Hypothesis Λ l g Y)(P':Titan Λ){X:List ι}{f:ℕ→ W (tent Y h)}{S:ℕ→Finset Cover}{Z:ℕ→Paint}(hp:∀ i:ℕ,Auth (tent Y h) (S i) (f i) (Z i))(pZ:∀ (i:ℕ)(N:Side),Z i N 1=lips (x i) X N 1)
local notation "Kₜ"=> tent Y h
omit ω in
private lemma furl_Z(T:Finset Cover):Tendsto (positionZ Y h T) atTop (𝓝 0):= by
 apply Tendsto.const_div_atTop; let L:=Λ.R.L; apply Tendsto.comp (g:=fun x:ℕ=>(x:ℝ)) tendsto_natCast_atTop_atTop; apply StrictMono.tendsto_atTop; apply strictMono_nat_of_lt_succ; intro i; change L.val^i < L.val^(i+1); have p:=pow_pos L.property i; have hQ:L.val≥4:=Λ.V.tallX; rw [pow_succ]; exact (Nat.mul_one (L.val^i)).symm.trans_lt (Nat.mul_lt_mul_of_pos_left (show 1<L.val by omega) p)
omit ω in
private lemma gymP(r ε:ℝ)(x y:ℂ)(n:ℕ)(t:0<r)(h:‖x-y‖ ≤ ε/(r^3)^n): ‖earthV r^n*x-earthV r^n*y‖ ≤ ε:= by rw [←mul_sub,norm_mul,norm_pow,earthV,norm_pow,Complex.norm_real,Real.norm_of_nonneg t.le]; exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by field_simp)
local notation "Ψ"=> ℕ → W Kₜ →ₗ[ℂ] ℂ
local notation "Ω" i:max=> absoluteP σ U D O i
include K R A S' P' hp pZ
lemma sleepy(i:ℕ)(e:0<ε): ∀ᶠ s in atTop, positionZ Y h (S i) s ≤ ε ∧ forall Φ:Ψ,Sphere Y h K R A Φ→ ‖earthV (r i)^X.length * Φ s (f i)-earthV (r i)^X.length *Prodigy (x i) X‖ ≤ ε:= by
 have t:=ω.basisE i; refine (((furl_Z Y h (S i)).eventually (ge_mem_nhds e)).and ((tuition Y (x i) (pZ i) h K R A S' P' (hp i) (show 0<ε/((r i)^3)^X.length by positivity)).mono fun s y Φ H=> gymP _ _ _ _ _ t (y Φ H))) -- tune
/-- genuine Gram costs at all late observing levels for this particular (fixed-order) Chisel tuple. Allows actual reflections in the mark by pZ stencil. -/
lemma furnace(e:0<ε): ∀ᶠ i in atTop, ∀ᶠ s in atTop, positionZ Y h (S i) s ≤ ε ∧ forall Φ:Ψ,Sphere Y h K R A Φ→ ‖earthV (r i)^X.length*Φ s (f i) - Ω X‖ ≤ ε:=by
 filter_upwards [(rehearP ω X).eventually (closedBall_mem_nhds _ (half_pos e))] with i p; filter_upwards [sleepy Y ω h K R A S' P' hp pZ i (half_pos e)] with s hx
 have hh:‖earthV (r i)^X.length*Prodigy (x i) X - Ω X‖ ≤ε/2:=by rw [← dist_eq_norm]; exact mem_closedBall.mp p
 exact ⟨hx.1.trans (half_lt_self e).le,fun Φ H=>(flightK _ _ _).trans ((add_le_add (hx.2 Φ H) hh).trans_eq (by ring))⟩
lemma starke: ∃ z:ℕ→ℕ,Tendsto z atTop atTop ∧ ∀ y: ℕ→ℕ,z≤ y →
 Tendsto (fun i:ℕ=>positionZ Y h (S i) (y i)) atTop (𝓝 0) ∧
 ∀ Φ:ℕ→ℕ→ W (tent Y h) →ₗ[ℂ]ℂ, (∀ i:ℕ,Sphere Y h K R A (Φ i)) → Tendsto (fun i:ℕ=> earthV (r i)^X.length * Φ i (y i) (f i)) atTop (𝓝 (absoluteP σ U D O X)):=by
 choose z Hz using fun i:ℕ=> eventually_atTop.mp (sleepy Y ω h K R A S' P' hp pZ i (one_div_pos.mpr (ω.basisE i))); let j i:= max i (z i); refine ⟨j,tendsto_atTop_mono (fun i=>le_max_left i _) tendsto_id,fun y t=>?_⟩; let H0(i:ℕ):= Hz i (y i) ((le_max_right ..).trans (t i)); have h:=Tendsto.const_div_atTop ω.comes 1
 refine ⟨squeeze_zero (fun i=>by unfold positionZ; positivity) (fun i=>(H0 i).1) h,fun Φ H=> ?_⟩; apply (rehearP ω X).congr_dist; refine squeeze_zero (fun _=>dist_nonneg) (fun i=>?_) h; rw [dist_comm, dist_eq_norm]; exact (H0 i).2 _ (H i)
omit hp pZ
lemma dimple(X:List ι): ∃ z:ℕ→ℕ,Tendsto z atTop atTop ∧ ∀ y:ℕ→ℕ,z≤ y → Tendsto (fun i=>positionZ Y h (band (x i) X) (y i)) atTop (𝓝 0) ∧ ∀ Φ:ℕ→ℕ→ W (tent Y h) →ₗ[ℂ]ℂ, (∀ i:ℕ,Sphere Y h K R A (Φ i))→ Tendsto (fun i:ℕ=>earthV (r i)^X.length * Φ i (y i) (courtI (x i) (tent Y h) X)) atTop (𝓝 (absoluteP σ U D O X)):=starke Y ω h K R A S' P' (fun i=>tribes (x i) Kₜ X) fun i N=> rfl
end
#print axioms dimple
#print axioms starke
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
