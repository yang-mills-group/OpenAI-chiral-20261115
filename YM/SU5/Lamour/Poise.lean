import YM.SU5.Lamour.Foyer
/-! # Stockyard Yard Sizes etc. Turn through ungauged temper. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 250000
noncomputable section
namespace YM.CF.Lamour.Bridge
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed -- remove Set.Notation
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N:Side}{a j d r:ℕ}{e ε δ z u θ y v γ ζ:ℝ}
section basis
variable {n:Type*}[LinearOrder n][Fintype n][Nonempty n]{P Q A T:Op n}{U: UNI n}
lemma lifted {x:Wave n}(V:UNI n)(p:Sea P x): Sea (twist V P) (acts (quantU V).val x):=by
 refine ⟨?_,(act_unit_norm ..).trans p.2⟩; rw [line_twist, ←Fock.swivel,p.1] -- tune
lemma held (g:IsStarProjection T)(h:twist U T=T)(o:0<z)(x:Wave n)(Q:FC n): boomR (acts (quantU U).val x) g o (twist (quantU U) Q)=boomR x g o Q:=by
 let V:= quantU U; let W:= acts V.val x; have he(u:ℝ):twist U (castV T u)= castV T u:=by rw [castV,map_smul,gate,map_add,map_smul,map_sub,map_one,h]
 have hh:modifyB T z (twist V Q)=twist V (modifyB T z Q):=by unfold V; rw [modifyB,modifyB,map_mul,map_mul,←quant_twist,←quant_twist,he,he]
 change inner ℂ W (acts (modifyB _ _ (twist V Q)) W)=_; rw [hh,show acts (twist V _) W= acts V.val (acts (modifyB T z Q) x) from (Fock.swivel V (modifyB T z Q) x).symm,show W=acts V.val x from rfl,act_unit_inner]; rfl
end basis
variable {M:Tulip.Male}{P:Pane N}{J S X:Finset (Seat N)}
local notation "💗" => cutM (Tset N)
local notation "🍬" => modesIn N
lemma here_one (g:Kea.Pad j N):∃ x:Wave (Single N), Sea (spar j M (1:Pane N)) x:=by
 obtain ⟨U,W,e⟩:=spot_projection (spar j M (1:Pane N)) (show IsStarProjection (spar j M (1:Pane N)) from (coasting g M) ▸ Kea.idol (Kea.too N) j M g.1) -- transport
 refine ⟨wedge U.val W, ?_,wedge_norm ..⟩; rw [e,act_twistLine,inner_self_eq_norm_sq_to_K,wedge_norm]; simp
lemma counts_c(z:Seat N→ SU.E)(X:FC (Single N)) : ‖twist (quantU (tradew N z)) X‖=‖X‖:= twist_norm ..
lemma tick_cut (N:Side):Sea (cutM (Tset N)) (mateK N):= (touchP N) ▸ tickB N
/-- Early optics. v price pull, ε prescription local after heat & card budget and mark accuracy. `θ` lakeR before. -/
structure Optic (j n k d:ℕ) (v ε θ l C R:ℝ):Prop where
 genuine : 0<v
 low : 4*v≤1
 theta: 0≤θ
 zephyr : 0<ε
 own: 180*(ε+ε+ε)≤v^2
 atT: 180*(ε+ε)≤v
 upper: ∀ {N:Side},Even N.val→Truth N j θ
 urban: ∀ {N:Side},Kea.Pad j N→ n≤ N.val →Margin N j ε k
 view : 180*(ε+ε+θ)≤ l
 lip : 1≤l
 spa : 1≤ j
 town: C*(4*v)*(4*l)^d ≤ R/4
 tide: 2^d*(C*((ε+ε)*plumeE d l l d)+ ε*l^d)≤ R/2
variable {B W l R Y C:ℝ}{n k:ℕ}
lemma choose_optic (p:1 ≤ j)(d:ℕ) (h:0≤C)(t:0<R) :∃ n k v ε θ l, Optic j n k d v ε θ l C R := by
 obtain ⟨x,g,u,T⟩:= stockyard p; let A:= 180*(1+x); have hv:1≤A:=by unfold A; linarith
 have ht: ∀ᶠ v:ℝ in 𝓝[>] 0, 4*v ≤ 1 ∧ C*(4*v)*(4*A)^d ≤ R/4:=by
    let U(v:ℝ):= C*(4*v)*(4*A)^d; exact Filter.Eventually.and ((continuousAt_const.mul continuous_id.continuousAt).continuousWithinAt.tendsto.eventually (ge_mem_nhds (show (4:ℝ)*0<1 by simp))) (( (show Continuous U from by unfold U; fun_prop).continuousAt.continuousWithinAt.tendsto ).eventually (ge_mem_nhds (show U 0<R/4 by simpa [U] using div_pos t (by norm_num : (4:ℝ)>0)))) -- tune
 obtain ⟨v,d',y⟩:= (ht.and self_mem_nhdsWithin).exists; change 0 < v at y; let f(e:ℝ):= 2^d*(C*((e+e)* plumeE d A A d)+e*A^d); let V:= v/360
 have hp:Continuous f:=by unfold f; fun_prop
 obtain ⟨e,⟨t₀,h₀,tr⟩,e'⟩: ∃ e:ℝ,(e≤ V ∧ e≤ v^2/540 ∧ f e≤ R/2) ∧ 0<e:= by
    have t₀:∀ᶠ x:ℝ in 𝓝[>] 0,x≤V:=eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (by unfold V; positivity))
    refine (Filter.Eventually.and (t₀.and (Filter.Eventually.and (eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (show 0< v^2/540 by positivity))) (hp.continuousAt.continuousWithinAt.tendsto.eventually (ge_mem_nhds (show f 0< _ from (by simpa [f] using half_pos t)))))) self_mem_nhdsWithin).exists -- tune
 obtain ⟨k,n,F⟩:=T _ e'; refine ⟨k,n,v,e,x,A,y,d'.1,g.le,e',by linarith, by unfold V at t₀; linarith,u,F,?_,hv,p,d'.2,tr⟩; unfold V at t₀; unfold A; linarith only [d'.1,t₀]
variable (H:Optic j n k d v ε θ l C R)
namespace Optic
include H
lemma reach (h:Kea.Pad j N)(hx:n≤N.val)(S:Finset (Seat N))(p:Sparkle N δ M j)(u:Guard P δ)(s:0<z)(t:z≤1)(g:Seat N→SU.E)(L: Clear S (Lattice.gauge g P) j M z (ε+ε)):
 let V:=sill N j M z P; let D:= modesIn N S; Bun (ray V (Tset N)) D D l ∧ (∀ X:Finset (Seat N),Distant (k+1) X S→Bun (ray V (Tset N)) (modesIn N X) D v)∧∀ i∈D, ‖acts (wish (tickA N) (here N j z M P) z (shadeK (Tset N) i)) (basisKet i)‖≤ v:=by
 intro V D; obtain ⟨a,b,w,K⟩:= Wat.pine (H.upper h.1) h p u g H.theta s t (add_nonneg H.zephyr.le H.zephyr.le) H.zephyr.le (H.urban h hx) L
 refine ⟨ray_cash H.lip (a.zen H.view) (b.zen H.view) _ D,fun X x=>pet_shop ((K X x).1.zen H.own) ((K X x).2.zen H.own) _, fun i hi=> ?_⟩; exact (w (shadeK (Tset N) i) _ hi).trans H.atT
lemma pity (g:Kea.Pad j N)(v:Distant 0 S S): Bun (ray (lake N j M) (Tset N)) univ (modesIn N S) l:=by
 have ht:= H.upper (N:=N) g.1 M; apply ray_cash H.lip
 all_goals have h:θ≤l:=H.view.trans' (by linarith only [H.zephyr,H.theta])
 exact fun i _=> (ht i).1.trans h; -- semicolon binds?
 exact fun i _=>(ht i).2.trans h
lemma pityR (g:Kea.Pad j N): Bun (ray (lake N j M) (Tset N)) (modesIn N S) (modesIn N S) l:=fun i ti=> (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>by positivity)).trans (pity H g (fun _ _ _ _=> Nat.zero_le _) i ti)
lemma port (S:Finset (Seat N))(Z X:FC (Single N))(h:‖X‖≤ C)(u:‖X-Z‖≤ε)(ht:(modesIn N S).card ≤ d)(p:Reed.Fine (Tset N) (modesIn N S) false X)(e:Reed.Fine (Tset N) (modesIn N S) false Z)(L:Kea.Pad j N)(vP:Sparkle N δ M j)(tX:Guard P δ)(s:0<z)(y:z≤1)(g:Clear S P j M z (ε+ε))(w:∃ U:Wave (Single N),Sea (spar j M (1:Pane N)) U ∧ ‖alleyR (mateK N) U Z‖≤R/4)(u':Wave (Single N))(p':Sea (here N j z M P) u'):‖X‖*(4*v)*(4*l)^d + ‖boomR u' (cutM_idp (Tset N)) s X‖ ≤ R:=by
 obtain ⟨U,t,e'⟩:= w
 let A:=here N j z M P; have he:Clad (spar j M (1:Pane N)) (💗) 1 1 (Kea.Dofu N (lakeK N j M)):=by rw [←touchP, coasting L M]; exact (pitch M H.spa L.1).1
 have hp:IsStarProjection A:=(draft_lit (vP.projection P tX) (Kea.cut_t N) s y).1
 let f:=boomR u' (cutM_idp (Tset N)) s; let B:= alleyR (mateK N) U
 have hy:lake N j M=laneP (💗) 1 (Kea.Dofu N (lakeK N j M)):= (touchP N) ▸ (pitch M H.spa L.1).2; let x:= pityR (M:=M) (S:=S) H L; have hz:= H.zephyr; obtain ⟨Xg,g'⟩:=liftleigh (H.upper L.1) g;
 have hm: ε+ε+θ≤l:= H.view.trans' (by linarith only [hz,H.theta]); have hQ: slant (💗) A z = sill N j M z P:= by rw [←touchP]; rfl
 have ha:= near_trust he hy t (tick_cut N) s hp p' (show 0≤ε+ε from (by positivity)) H.lip x d ht (zero_le_one.trans H.lip) (fun i ti j tj => hQ ▸ (Wat.ray_p (_root_.YM.CF.Lamour.Wat.zen Xg hm) (g'.zen hm) _ _ _ tj)) (fun i _ j tj=> hQ ▸ ray_toll g.reach g.fetch (le_refl (0:ℕ)) _ i _ tj) X Z p e
 have hd: ‖f X-B Z‖≤R/2:= ha.trans (H.tide.trans' (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right h (mul_nonneg (show 0≤ε+ε from by positivity) (plume_non (zero_le_one.trans H.lip) (zero_le_one.trans H.lip)))) (mul_le_mul_of_nonneg_right u (pow_nonneg (zero_le_one.trans H.lip) _))) (by positivity))) -- ha instantiated a free
 have hl:= norm_le_norm_sub_add (f X) (B Z); change ‖B Z‖≤ _ at e'; let z:= H.lip; have h_:0<v:=H.genuine; let u:= R; change _+‖f X‖≤ _; apply (add_le_add (H.town.trans' (by gcongr <;> first| positivity| assumption)) hl).trans; linarith only [e', hd]
end Optic
end YM.CF.Lamour.Bridge
#print axioms YM.CF.Lamour.Bridge.Optic.port
#print axioms YM.CF.Lamour.Bridge.choose_optic
