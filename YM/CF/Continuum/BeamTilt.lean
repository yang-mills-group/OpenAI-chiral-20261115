import YM.CF.Continuum.RightAngle
import YM.CF.Continuum.Billhead
import YM.CF.Mint.Locket

/-!
# Pointwise comparisons INSIDE on the localized holonomy budget

Use the conditional geometry `towards`. Wick mixed estimates
 for actual tilt/gauge and the nontrivial FiniteGaugeData budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter Metric Finset NormedSpace Cube SU Mint Mint.Roe Lattice RG Wilson Laurent Peaks Spire Brace Vault Dial Paige Pressure
open Rush Tulip Gall Graph Phase Fock Lat Flare Emu Skye Scree MeasureTheory Nacre Laic Girt Pastry Nova Branch
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192

variable {m B N : Side}
abbrev GlowLeg:=Option Component
def glowRead (f:GlowLeg) (s:Site N) : Evaluation N := f.elim 1 fun c=> current N c.fam s c.up c.down
variable (F:GlowLeg) (s:Site N)
lemma glowRead_local : glowRead F s ∈ localObs N ∅ {s}:=by
 cases F with | none=> exact (localObs ..).one_mem | some a=>exact current_local _ _ _ _ a.hu a.hd
lemma no_link (x y:Pane N): glowRead F s x= glowRead F s y:=by cases F <;> rfl
section bill
variable {p: Phys N} {a b:ℝ}(Q:Pane N)(h: Gall.Yep a (mateK N) p b)(f:F=F)
def rateLeg(a:ℝ):=45*(1+a^2)
lemma glowRead_cost(U:Pane N): ‖glowRead F s U‖≤ 45:=by
 cases F with
 | none=> change ‖(1:FC (Single N))‖≤45; norm_num
 | some F=>
    change ‖current N F.fam s F.up F.down U‖≤ _; rw [current_words]; apply (norm_sum_le ..).trans -- remove
    apply le_trans (sum_le_sum (g:=fun _=>1) (fun j _=>?_)) ?_; · rw [sum_const,nsmul_eq_mul,colors_card,mul_one]; unfold dimf; split<;> norm_num
    refine (norm_mul_le ..).trans ?_; rw [takeF,norm_star]; exact (mul_le_mul (cost_u _) (cost_u _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
lemma pic_gall (k:ℝ)(x:Phys N)(b:ℝ)(h:Pic.Yep k (mateK N) x b): Gall.Yep k (mateK N) x b:=by
 intro v; have he:unitsC (Single N) (v.map artW)=1:=by induction v with| nil=>simp [unitsC]| cons a b h=> unfold unitsC at *; simp only [List.map_cons,List.prod_cons, artW, show ∀ i: Single N, ‖basisKet i‖=1 from fun i=> (by simp),one_mul] at *; exact h
 have ht:=h (v.map artW); unfold Flare.size_k at ht; rw [he,List.length_map,one_mul] at ht; exact (by unfold rollC at *; rw [List.map_map] at ht; exact ht)
private lemma put_pays {n:Type*}[Fintype n][LinearOrder n](i:n)(a:ℝ)(p:0≤a): Pays a (put i) a:=by simpa [Gall.pack,artW,ton,Fock.creed] using Pays.tone (false,i) p
private lemma take_pays {n:Type*}[Fintype n][LinearOrder n](i:n)(a:ℝ)(p:0≤a): Pays a (takeF i) a:=by simpa [Gall.pack,artW,ton,Fock.creed] using Pays.tone (true,i) p
lemma glowRead_pay (h':0≤a) : Pays a (glowRead F s Q) (rateLeg a):=by
 cases F with
 | none=> exact Pays.uno.weigh (by unfold rateLeg; nlinarith) h'
 | some F=>
    change Pays _ (current N F.fam s F.up F.down Q) _; rw [current_words]; refine (Pays.sumT _ _ (fun _=>a*a) ?_).weigh ?_ h'
    · intro j _
      exact Pays.mul (put_pays ((s,F.up),j) _ h') (take_pays ((s,F.down),j) _ h')
    rw [sum_const,nsmul_eq_mul,colors_card]; unfold rateLeg dimf; split<;> push_cast <;> nlinarith
lemma glowRead_priced (h':0≤ a) (t:0≤b)(h: Gall.Yep a (mateK N) p b) : ‖oneField Q p (glowRead F s)‖ ≤ b*rateLeg a:=by -- ClassChoice replace with oneField
 rw [mul_comm b]; exact ((glowRead_pay F s Q h').2 _ _ b t h).low
end bill
local notation "Λ" => CSide m B
variable {J :Side}{a b c w η r k z t μ x D L d K R s' E C y v vA u C' vB tQ tL tB:ℝ}{j n n₀:ℕ}{O:Odd J.val}{Y:Pricing j J O (Thread j)}{P:Grasp Y B d}{hp:Pearl P}
variable (Q:Pic.Span hp K b v C' z s' n)(A:GramM (mid m B))(X:Loom (mid m B))(p:SkinT A X d)(ℓ: n≤(CSide m B).val)
variable (U: Orbit (mid m B))
open Sods
section
variable (I:Evaluation Λ)
include ℓ Q
lemma tilt_cost (h:0<t)(v':t≤1)(u:(CSide m B).val^10*t ≤v)(g:Cart (Domain m B))(hg:lawnK (gauge g U.1) (Kea.tax (needles (mid m B))) t) (s:Site (mid m B)): ‖oneField U.1 (changeM P U.1 A.J.M) (glowRead F s)-oneField U.1 (changeM P (Kea.tax (needles Λ)) A.J.M) (glowRead F s)‖ ≤ (C'*(mid m B).val^10*t*Kea.angel m P A.J.M)*rateLeg (K*(mid m B).val):=by
 let k:=(mid m B); let W:=gauge g U.1; let T:=changeM (m:=m) P U.1 A.J.M; let V:=changeM (m:=m) P W A.J.M; let M:=mateK k; let F':= glowRead F s; let B':= F' U.1
 have ge := spiral _ (needlesSlow k); obtain ⟨Qv,QW⟩:=Q.plan _ ℓ; obtain ⟨hu,H⟩:= Q.pale m ℓ A.J.M (needles Λ) ge W t h v' u hg; have he: Guard U.1 d:=(by have ht:=hu.cov g⁻¹; unfold W at ht; rwa [windy,inv_mul_cancel,windy_u] at ht)
 let N:=quantU (tradew _ g); have hv:inner ℂ M (acts B' V)=inner ℂ M (acts B' T) := by
   have hv:B'=twist N B':=(no_link F s _ W).trans ((mem_allObs ..|>.mp (fits_all (glowRead_local ..))).2.2 g U.1)
   have hl:V=acts N.val T:= Hive.honey_x hp Q.stmt Qv Q.p he g
   nth_rw 1 [hv]; rw [hl,←Fock.swivel]; nth_rw 1 [←show acts N.val M=M from Girt.mastC _]; apply act_unit_inner
 let S:=changeM (m:=m) P (Kea.tax (needles k)) A.J.M
 change ‖inner ℂ M (acts B' T) - inner ℂ M (acts B' S)‖≤_; rw [←hv, ←inner_sub_right, ←map_sub]; have hb:= Kea.angel_p hp Q.stmt Qv Q.p Q.eP A.J.M QW; exact glowRead_priced F s U.1 (by have t:=Q.kP; positivity) (by have t:=Q.cP; positivity) (pic_gall _ _ _ H)
end
include Q ℓ p
-- hu can be from caesar w.Roll+f.wear; no need from tilt
lemma tilt_beam (T: Orbit (mid m B))(W: Ledger R u η r C A)(h:T∈ Lace A)(t:1≤ R)(hp:0 ≤ r)(hs:0≤vA)(d:HelpP T.1 vA r)(hC:0 ≤ C)(hx:pittance (mid m B) vA C≤1)(s:Site (mid m B)) (hk:0≤k)(hy:0≤y)(hu:Gall.Yep k (mateK Λ) (changeM (m:=m) P T.1 A.J.M) (y*Kea.angel m P A.J.M))(ht:∀ i: LeanV (Single (mid m B)), Pays k (drawT (spar j A.J.M T.1) i) R) :
 ‖oneField T.1 (Graph.beam A P X T) (glowRead F s)-oneField T.1 (changeM (m:=m) P T.1 A.J.M) (glowRead F s)‖ ≤ ((baton (mid m B) u vA C k)*(y*Kea.angel m P A.J.M))*rateLeg k:=by
 let Y:= (mateK (mid m B)); let Z:=glowRead F s; let M:= changeM (m:=m) P T.1 A.J.M; obtain ⟨v,w,q⟩:=p.wave; have he: X T=T.1:=p.high _ h; have hv:= Q.plan m ℓ; let K':=mile j A X T -1; have hh:=ridge (j:=j) (X:=X) W T ((show X T=T.1 from he) ▸ d) hs hp (zero_le_one.trans t) hk hC ((P.broadness _ hv.1 A.J.M).projection _ (q.paid T)) (show flags _ T.1=∅ from h) hx (he ▸ ht)
 let Kt:= Kea.angel m P A.J.M; have hK:0≤ y*Kt:=mul_nonneg hy (Kea.angel_p ‹Pearl P› Q.stmt hv.1 Q.p Q.eP _ hv.2).le
 unfold Graph.beam oneField; rw [←inner_sub_right,←map_sub,he]; rw [show acts _ _ - _= acts K' M from ?_]; exact glowRead_priced F s T.1 hk (mul_nonneg hh.1 hK) (hh.2 _ _ _ hK hu)
 unfold K' M; rw [act_sub,act_one]
end YM.CF.Window
