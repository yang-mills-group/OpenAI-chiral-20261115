import Bay.D.Davit
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Resonance Brecht Circuit
open CF.Onyx CF.Ember
open Stationary (Gaia)
open Maxwell

abbrev latX:= YM.basis 3
lemma latX_n:‖latX‖=1:=by unfold latX;simp
lemma latX_c:latX≠0:=norm_pos_iff.mp (latX_n.symm ▸ (show 0<(1:ℝ) by norm_num))
abbrev loom_price:ℝ:=4*Maxwell.normal
lemma loom_price_c:0<loom_price:=by unfold loom_price;have := Maxwell.normal_pos; positivity
def decks: Fin 6 → PlaqAxes:= ![⟨(0,1), by decide⟩,⟨(0,2), by decide⟩,⟨(0,3), by decide⟩,⟨(1,2), by decide⟩,⟨(1,3), by decide⟩,⟨(2,3), by decide⟩]

lemma decked : ∀P:PlaqAxes,∃i,P=decks i:=by decide

lemma gannet(P Q:PlaqAxes) :
  specter P Q latX= 
    if P=Q then (loom_price:ℂ)*orient Q else 0:=by
 simp only [specter, bareCurl,Pi.sub_apply, Bare.opp_grad latX_c, second_Green latX_c,
    latX_n]
 obtain ⟨i,rfl⟩:=decked P
 obtain ⟨j,rfl⟩:=decked Q
 fin_cases i <;> fin_cases j <;> norm_num [decks, loom_price,orient,latX] <;>
      simp (config:={decide:=true}) <;> ring


abbrev meander(m:ℕ):ℝ:=m+1
lemma meander₀(m:ℕ):0 < meander m:=by unfold meander;positivity
lemma meander_t:Tendsto meander atTop atTop:=
  (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add tendsto_const_nhds

structure Tine (m:ℕ)(n:Side)(R:ℝ)(z:Cover):Prop where
  large: meander m ≤ R
  fine: R * Ember.pinch n ≤ (meander m)⁻¹
  place(i:Axis): |riseX R z i - latX i| ≤ (meander m)⁻¹

variable {σ v ε:ℝ}
lemma gannet_see(q:Clip)(h:0<σ)(u:0<v)(η:ℝ)(t:0<ε)(P Q:PlaqAxes):
   ∀ᶠ m:ℕ in atTop, ∀ (n:Side) (R:ℝ) (z:Cover)(M:Bed),
   Even n.val → Tine m n R z →
   M.covered σ v → Floor M q n η v →
      ‖magnify M R (plaquette P) (plaquette Q) z n-specter P Q latX‖≤ε:=by
   by_contra ht;push Not at ht
   obtain ⟨g,b,c⟩:=extraction_of_frequently_atTop ht
   choose S R z M f B A C H using c
   have p:=meander_t.comp b.tendsto_atTop
   have y:Tendsto (fun i=>(meander (g i))⁻¹) atTop (𝓝 (0:ℝ)):=tendsto_inv_atTop_zero.comp p
   have l(i):0<R i:=(meander₀ _).trans_le (B i).large

   have yard:Yard S R:= ⟨l,tendsto_atTop_mono (fun i=> (B i).large) p,squeeze_zero (fun i=>mul_nonneg (l i).le (Ember.pinch_pos _).le)
    (fun i=>(B i).fine) y,f⟩
   have hX:Tendsto (fun i=>riseX (R i) (z i)) atTop (𝓝 latX):=by
      have he:Tendsto (fun i=>((riseX (R i) (z i)).ofLp)) atTop (𝓝 latX.ofLp):=by
         apply tendsto_pi_nhds.mpr
         intro j
         apply Metric.tendsto_nhds.mpr
         intro d s
         filter_upwards [y.eventually (gt_mem_nhds s)] with i L
         rw[Real.dist_eq]
         exact ((B i).place j).trans_lt L
      exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp he
   have:=Circuit.mercury P Q yard hX latX_c A C h u
   obtain ⟨i,hi⟩:=(Metric.tendsto_nhds.mp this ε t).exists
   rw[dist_eq_norm] at hi
   exact lt_asymm hi (H i)

def ribbon(ρ:ℝ):ℝ:=ρ^2*loom_price
variable {n:Side}{H:Bed}
abbrev Upbraid(q:Clip)(σ v η:ℝ)(m:ℕ)(d:ℝ):Prop:=
 ∀ (P Q:PlaqAxes)(n:Side)(R:ℝ)(z:Cover)(M:Bed),
   Even n.val → Tine m n R z→ M.covered σ v→ Floor M q n η v →
      ‖magnify M R (plaquette P) (plaquette Q) z n-specter P Q latX‖≤d

lemma gannets(q:Clip)(h:0<σ)(u:0<v)(η:ℝ)(t:0<ε):
 ∃m:ℕ, Upbraid q σ v η m ε:=
  ((eventually_all.mpr fun P=>eventually_all.mpr fun Q=>gannet_see q h u η t P Q)).exists

variable {i j:Cella n}
lemma gannet_altar :
  (sch (G:=T4) i.2.2 j.2.2:ℂ) * orient j.2.1 * specter i.2.1 j.2.1 latX =
    loom_price * relive i j:=by
 rcases i with ⟨x,P,a⟩
 rcases j with ⟨y,Q,b⟩
 rw[gannet]
 simp only[sch,relive,reed,Prod.mk.injEq,Complex.ofReal_mul]

 by_cases u:a=b <;> by_cases t:P=Q <;> simp [u,t]
 unfold orient
 split <;> norm_num

variable {q:Clip}{Z:PathData T4}{η f l D:ℝ}(B:Z.Bounds q η f l)(P:Attached H Z)
lemma gannet_pair {d R:ℝ}{b c:Site n}{ρ:ℝ}{m:ℕ}
   (A:Upbraid q σ v D m d)
   (y:H.covered σ v)(L:Floor H q n D v)(h:0<σ)
   (t:Even n.val) (u:|ρ|≤2)
   (p:∃z,Tine m n R z ∧ i.1+b-(abaft j.1 j.2.1+c)=wrap n z) :
 ‖(R:ℂ)^4* hashes (south B P b ρ) (north B P c ρ) i j - (ribbon ρ:ℂ) * relive i j‖ ≤ 4*d:=by
 obtain ⟨z,a,e⟩:=p
 let V:=(ρ:ℂ)^2 *sch (G:=T4) i.2.2 j.2.2 * (orient j.2.1)
 have hc:‖V‖≤4:=by
   unfold V
   simp_rw [norm_mul, norm_pow,Complex.norm_real,Real.norm_eq_abs,nor_sign,mul_one]
   unfold sch; split
   · simpa using ((pow_le_pow_left₀ (abs_nonneg _) u 2).trans_eq (by norm_num : (2:ℝ)^2=4))
   norm_num

 have hp: (ribbon ρ:ℂ)* relive i j=V*specter i.2.1 j.2.1 latX:=by
    unfold V ribbon
    rw[Complex.ofReal_mul,Complex.ofReal_pow,mul_assoc,←gannet_altar]
    ring
 have hy: rimble n H (i.1+b,plaquette i.2.1) (abaft j.1 j.2.1+c,plaquette j.2.1) =
    rimble n H (wrap n z,plaquette i.2.1) (0,plaquette j.2.1):=by 
    rw[rimflare n H _ _ _ e,rimflare n H _ _ z (sub_zero _)]
 rw [hash_price B P b ρ c i j L y h t,hp,hy]
 change ‖(R:ℂ)^4*(V*_)-_‖≤_
 rw[mul_left_comm,←mul_sub,norm_mul]
 exact mul_le_mul hc (A _ _ _ _ _ _ t a y L) (norm_nonneg _) (by norm_num)

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.gannet_pair
