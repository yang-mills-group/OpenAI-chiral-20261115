import YM.CF.Chaff.Image
import YM.CF.Fief.Vex
import YM.CF.Hype.Ace
import YM.CF.Ione.Mesh
import YM.CF.Fief.Lucid
import YM.CF.Char.Gel
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
open MultiNext.SignedSource
variable (o:Seat (CSide m B))(y:o∈S) (t:Grove (terr _) S)
variable {r Y V x μ b θ C' ρ:ℝ}
open Gloss Maize Ione Salt Hive Vow
variable {σ τ:ℝ}{d:ℕ}
open Fief sizeK
lemma upR(C:ℝ)(K:ℕ)(L:Side) : sizeK L 1 fun x=> C*(ailed (radiusB x)*temp x)+temp x*(1+ (radiusB x:ℝ))^K:=by
 have hv:sizeK L 0 fun x=> ailed (radiusB x):=by simp only [ailed,Nat.cast_mul,Nat.cast_ofNat]; exact ((((Bcash L).scale (2:ℝ)).scale 2 |>.accrue (mild L 1)).powC 5|>.scale 16).tint (mild L _)
 exact (((hv.tint (tempo L)).scale C).accrue ((tempo L).tint (((mild L 1).accrue (Bcash L)).powC _)))
lemma TicX (k t:ℕ)(pK:1≤k)(L:Side)(p:0<e)(C1:VStar k K)(q:1≤K):∃ C:ℝ,0 < C ∧ ∃ κ:ℝ→ℝ,sizeK L 1 κ∧∀ᶠ x in atTop, ∀ P:BudgetPoint,P.power=t → P.order=k → P.threshold=temp x → P.B=radiusB x → Nice k P e K C (κ x):=by
 obtain ⟨g,h,gQ,hQ,b⟩:=Next.Fluctuations.log_chart_cost SU.group; obtain ⟨d,D,z,u,G'⟩:= braved pK; obtain ⟨s,r,S,B⟩:=toll_y p; let V:=fun x=>g*(ailed (radiusB x)*temp x)+temp x*(1+(radiusB x:ℝ))^t; have hv: sizeK L 1 V:= upR _ _ L; let K1:=fun x=> D*V x; have hh:= hv.scale D
 have he:∀ᶠ x in atTop,V x≤ g*h:= hv.spine.eventually (ge_mem_nhds (mul_pos gQ hQ))
 refine ⟨g,gQ,K1,hh,?_⟩; filter_upwards [he,hv.spine.eventually (ge_mem_nhds z),hh.spine.eventually (ge_mem_nhds (half_pos r)),Work.E01.radiusB_tendsto.eventually_ge_atTop 12] with x t0 t1 t2 t3 U uP bV yV H1
 have hV:leanP U g=V x:=by simp only [leanP,riseH,black_t,uP,yV,H1,V]
 rw [←hV] at t0 t1; have hΔ:g*black_t U≤g*h:= (le_add_of_nonneg_right (mul_nonneg U.threshold_pos.le (by positivity:0≤(1+(U.B:ℝ))^U.power))).trans t0
 refine ⟨bV,H1.symm ▸ t3,⟨s,r,S,t2,(fun m B' i=> B _ _ (guard0 le_rfl) i)⟩,⟨_,b,le_of_mul_le_mul_left hΔ gQ⟩, gQ.le,⟨d,D,z,u,by unfold K1; rw [hV], G', t1⟩, C1,q⟩
lemma blight (L:Side)(p:0<b): sizeK L 2 (fun x=>Real.exp (-b*radiusB x)):=by
 refine (val_gain L (2*b) (by linarith) 1 one_pos 2).cost_d (Eventually.of_forall fun x=>?_); unfold Newt.tollE; simp_rw [abs_of_pos (Real.exp_pos (_:ℝ))]; apply Real.exp_monotone; have he:(↑(Stores.till x/1):ℝ) ≤ (radiusB x:ℝ):= Nat.cast_le.mpr (by unfold Stores.till; omega)
 nlinarith
lemma limp (L:Side)(p:0<σ)(v:σ<1):sizeK L 2 fun x=> σ^radiusB x:=by
 let f:= Real.log σ; have hp:f<0:=Real.log_neg p v; apply (blight L (b:=-f) (by linarith)).cost_d; filter_upwards with x; apply le_of_eq; apply congrArg abs; rw [neg_neg,mul_comm,Real.exp_nat_mul]; unfold f; rw [Real.exp_log p]
abbrev hintF(P:BudgetPoint)(t n:ℕ)(x r:ℝ):= P.power=t ∧ P.order=n ∧P.threshold=temp x ∧P.B=radiusB x∧P.supportExponent=r
structure Opera(P:BudgetPoint)(n:ℕ)(e a H Y K M c':ℝ):Prop where
 costs : ∃ T r U θ b μ:ℝ, Nice n P e K T θ ∧ 1 ≤ H ∧0 ≤ Y ∧0 ≤r ∧r≤1∧0 ≤U∧0≤μ∧μ*mealz ≤ b ∧Y*H⁻¹ ≤ r*μ ∧ (∀ (i:ℕ)(v:ℝ), 0 ≤ v → payP P i*composeCost P.order v (riseH P i)+v ≤ U*(Real.exp (b*i)*v)) ∧0<b∧2*P.supportExponent*Fief.tileN 3≤ b*P.B∧4*b=a ∧ c'= HopeN P b U r θ * M
lemma Garn (n t:ℕ)(p:1≤ n)(L:Side)(s:ℝ)(h:H≥1)(k:VStar n K)(q:1≤K)(e0:0<e)(a0:0<a)(hx:0<σ)(hp:σ<1) (u:ℝ→ℝ) (he:sizeK L 0 u):∃ μ:ℝ→ℝ,sizeK L 2 μ ∧∀ᶠ x in atTop,∀ P:BudgetPoint,hintF P t n x s →Opera P n e a (bond σ H (radiusB x)) H K (u x) (μ x):=by
 let b:=a/4; have h0:0<b:=by unfold b; positivity
 obtain ⟨C,y,f,F,w⟩:=TicX n t p L e0 k q; obtain ⟨A,B,T⟩:=tuneR t n h0; let v:= b/(mealz+1:ℝ); have hu:0<v:=by unfold v; positivity
 let r(x:ℝ):= v⁻¹*σ^radiusB x; have hr:sizeK L 2 r:=(limp L hx hp).scale _;
 let M:= Real.exp (s*Fief.tileN 3); let Z:= composeCost n 4 1; let W:=fun x=> Z*f x^2+ Real.exp (-b* radiusB x)*A+r x*A
 have hW:sizeK L 2 W:= (((show sizeK L 2 (fun x=> f x^2) from (F.square 2)).scale Z).accrue ((blight L h0).tint (sizeK.mild L A))).accrue (hr.tint (sizeK.mild L A))
 have hh:Tendsto (fun x=> b*(radiusB x:ℝ)) atTop atTop:= Tendsto.const_mul_atTop h0 (tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto)
 refine ⟨_,((hW.scale M).tint he),?_⟩; filter_upwards [hh.eventually_ge_atTop (2*s*Fief.tileN 3),w,(hr.low (show 1≤2 from one_le_two)).spine.eventually (ge_mem_nhds zero_lt_one)] with x y w l P z
 have hP:0<H:=zero_lt_one.trans_le h; obtain ⟨c,n',t',s',d'⟩:=z; refine ⟨C,r x,A,f x,b,v,w _ c n' t' s', bond_good h hx hp _, hP.le,mul_nonneg (inv_pos.mpr hu).le (pow_nonneg hx.le _), l, B,hu.le,?_ ,?_,T P c n',h0,by rw [s',d']; exact y,by unfold b; ring,?_⟩
 · have he:v*(mealz+1:ℝ)=b:=div_mul_cancel₀ _ (by positivity); rw [mul_add,mul_one] at he; rw [←he]; linarith
 · unfold bond r; apply le_of_eq; field_simp
 change M*W x*_= _; unfold W HopeN Z M; rw [n', d',s']; unfold composeCost; ring
end YM.CF.Chaff
