import YM.CF.Buffered.Sestina
import YM.CF.Buffered.Corollary
/-!
# Assemble Bill-E. Actual readings on the Cone, ratios not amplitudes, two observables on same pivot.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 550000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concert
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RG Wilson Branch
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Vale Skye Stencil
open Further.PhysicalPeriodLimitF933 Macrame Crust Push.GridApprox Tenant Laurent Bloch Next.Free Fir Peaks Scree Drapes Tap Dial Reflect Window
open Mail Mail.Grok Ballad Ballad.Markwalk Wings Py
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{C: Conveyor K}{J:Tiling K}{x k:ℕ}{V:SpanCal K}(W:Printed K C J V){e:ℝ}(p:Venue V e)(Z:Rates p J)(z:ℤ)
local notation "o"=>K.q
local notation "m₃"=>K.q* (3:Side)
local notation "Z'"=>J.native_ord
local notation "s"=>mesh J.d' K.R.L x
local notation "E"=>Ballad.Venue.towards K.B (Original.primary K) z
local notation "Vδ"=>K.ℓ+p.width+1
abbrev Rented (p: Venue V e)(J:Tiling K)(z:ℤ) := Melody.Budget (Ballad.Venue.towards K.B (Original.primary K) z) (gaugedTop K J 0) (K.ℓ+p.width+1) 0
variable (G:Rented p J z)
local notation "Y"=>E
variable {m t:Side} (F:Flipbook K J C x)(X:LacePoint K C J) (A: K.Allowed K.q x)(I: K.Allowed (K.q*3) x)(R:K.Allowed m x)
include G p z
lemma rents {h:K.takes m}(b:Bool): AtSupport false (sageF J 0 h) ((E).goal b):= allowance (A:=E) G (show K.ℓ≤ Vδ from by omega) h E (.home) b -- tune G duplication
include R X F A
lemma rolls (u:m=K.q*t)(b:Bool) (Q:Badge (mesh J.d' K.R.L x) K.B) (v:stamps (J.native_ord o A.1 x) 0 (postV C o x x ((E).goal b)) Q) (g:∀ (a b:Locale s K.B),a.1=b.1→ Q.label a=Q.label b): stamps (Z' m R.1 x) 0 (postV C m x x ((E).goal b)) Q := by
 refine child_reach (Z' _ R.1 x) (Z' _ A.1 x) (screen₂ K x u) ((F.frame m R).onGlass J le_rfl (rents p z G b)) (gauged K) (dressedV J x x R A u F X (rents p z G b) (rents p z G b) (chosen (certV K 0 u) (orderV K J 0 A.1) (by omega:0< K.ℓ+p.width+1) E G b) le_rfl) v g
local notation "Zm"=> F.frame m R
local notation "Zq"=> F.frame o A
local notation "Z₃"=> F.frame m₃ I
local notation "β"=> (C.warm o x x).beta
local notation "P"=> K.K.top.clip
local notation "vF"=> launchK K x
omit p z X G
lemma singleV (E_:Melody K.B K.vertex)(b:Bool)(Q:Badge (mesh J.d' K.R.L x) K.B)(v:stamps (Z' m R.1 x) 0 (postV C m x x (E_.goal b)) Q) : Ticket.singleZ ((F.frame m R).permit J) Q P β vF=markedRead (E_.goal b) (C.loom m 0) (denZ (C.warm m x 0) K.P (C.loom m 0)) :=by rw [← F.tilt_equal R A x le_rfl,(Zm).trips_num (E_.global b) le_rfl, (Zm).pays_num _ ((Zm).global le_rfl (E_.global b)).env]; exact Ticket.self_log ((F.frame m R).permit J) _ _ _ _ v
include p z G
omit R
lemma certificate (Q: Badge (mesh J.d' K.R.L x) K.B) (b: Bool) (v: stamps (Z' o A.1 x) 0 (postV C o x x ((E).goal b)) Q) (r:Rail (Uniform (J.qcount K.q)))(T:Melody K.B K.vertex)(y:MarkPath J K.q E r T): stamps (Z' o A.1 x) r (postV C o x x (T.goal b)) (Q.reflected r):=by
 induction y with
 | home=> rw [Badge.reflected_zero]; exact v
 | @marches r T t i v' ih=> rw [← T.mirror_goal b i (upstairs' _ r i),(Zq).trips_ref (T.global b) le_rfl, plane_set J x, sign_shade (Z' o A.1 x)]; exact stamps_ref _ _ ih i v'
-- sums & orders
omit F A G p z
private lemma festival_write {B N:Side}{I:Type*}{e:ℕ} (Q:I→Melody B e)(L:List I)(b:Bool): Melody.festival (N:=N) Q b L=(L.map fun i=> (Q i).goal b).prod:=by funext x; induction L with|nil=> rfl|cons i L ih=> exact congrArg (fun z=> (Q i).goal b x * z) ih
lemma square_cost (Q:Melody K.B K.vertex)(b:Bool)(x:Fields (K.c m)): ‖Q.goal b x‖ ≤ |Melody.cuts K.vertex 0|+1:=by have ht:= Melody.festival_norm (N:=K.c m) (fun _:Unit=> Q) b [()] x; rw [festival_write] at ht; simp at ht; exact ht.trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))
include p z G F A
lemma responds (Q: Badge (mesh J.d' K.R.L x) K.B) (b: Bool) (v:stamps (Z' o A.1 x) 0 (postV C o x x ((E).goal b)) Q) : ∃ (D:Rail (Uniform (J.qcount o))→Melody K.B K.vertex)(L:List (Rail (Uniform (J.qcount o)))), (∀ i, MarkPath J o E i (D i)) ∧ L.Nodup ∧ L.length=clicks J o ∧ Ticket.moment ((F.frame o A).permit J) Q P β vF=markedRead (Melody.festival D b L) (C.loom o 0) (denZ (C.warm o x 0) K.P (C.loom o 0)):=by
 choose D hv using Markwalk.receives J A.1 E; let L:= (univ:Finset (Rail (Uniform (J.qcount o)))).toList; have he:L.length=clicks J o:=by simp [L,clicks,Rail, Axis,Uniform];
 refine ⟨D,L,hv,nodup_toList _,he,?_⟩; let G'(i):= (D i).goal b (N:=K.c o); have ht(i): AtSupport false (glass J 0 (r:=i) A.1) (G' i):= allowance (A:=E) G (show K.ℓ≤Vδ from by omega) A.1 _ (hv i) b; have hf:= ((Zq).backed J G' L ht).mono (subset_univ _)
 rw [festival_write,(Zq).trips_num (show AtSupport false univ (L.map fun i=> (D i).goal b).prod from hf) le_rfl, (Zq).pays_num _ ((Zq).global le_rfl hf).env,(Zq).coat_prod J le_rfl G' L (nodup_toList _) ht]; exact Ticket.coat_y _ _ _ _ _ (fun i=> postV C o x x (G' i)) L (by simp [L]) (nodup_toList _) (fun i=> certificate p z G F A Q b v i _ (hv i))
-- ratios-bounded first-tiled. declare conductor of readability uniform upper
include X Z W
omit F A
lemma showtime : ∀ᶠ n in atTop, ∀ m:Side, K.Allowed m n → ∀ b:Bool,‖atZero K.P (C.warm m n) (C.loom m) ((Original.primary K).goal b)‖ ≤ e/4:=by
 obtain ⟨u,U⟩:= W.spring (big_one K) W.window_q; obtain ⟨g,G'⟩:=W.spring (big_three K) W.window_3q
 filter_upwards [sound_stage p W Z,eco p W Z,W.sizes, U,G', K.eventually_allowed (big_one K),K.eventually_allowed (big_three K)] with n V e' ⟨T_⟩ h h_ H A; intro m R b
 obtain ⟨k,X',v⟩:= R.1; let a:= T_.frame m R; let Y':=T_.frame o H; let t:= T_.frame m₃ A;
 have ht:=rents p z G (h:=H.1) b
 obtain ⟨W',H',w⟩:= Wings.dye (A:=(J.native_ord o H.1 n)) (gauged K) (Y'.onGlass J le_rfl ht); have hm:=u.trans_le h.1; have h₃ :=g.trans_le h_.1
 let sq:= barestar C o n; let sm:=barestar C m n; let bQ:= barestar C (K.q*3) n; let xβ:= (C.warm o n n).beta; let qμ:=Y'.permit J
 have hx:0<sq:= (same_sign C).1 hm; have hY:0<bQ:=(same_sign C).1 h₃; let Q':=launchK K n
 have he:sq= ‖qμ.moment 1 P xβ Q'‖:=T_.price_scale H H; have ha:0<‖Ticket.moment (t.permit J) 1 P xβ Q'‖:= T_.price_scale A H ▸ hY
 have Hp:= p.p; have hy:0< e/8:=by positivity
 obtain ⟨D,L,f,d,r,Hq⟩:= responds p z G T_ H W' b H'; let j:= clicks J o
 have hα: ‖qμ.moment W' P xβ Q'‖≤ (e/8)^j*sq:=by
    have hy':0 < (CSide (mesh J.d' K.R.L 0) K.B).val:=PNat.pos _; have hc:(J.qcount o).val ≤ (K.c o).val:= (show (J.qcount o).val ≤ (CSide (mesh J.d' K.R.L 0) K.B).val * (J.qcount o).val from Nat.le_mul_of_pos_left _ hy').trans_eq (J.native_ord o H.1 0|>.spirit K.B|>.ratio.symm);
    have Hk: ‖atZero K.P (C.warm o n) (C.loom o) (Melody.festival D b L)‖ ≤ (e/8)^j := V (Rail (Uniform (J.qcount o))) b (fun x:Single (K.c o)=> Crust.Grid.ledge (orderV K J 0 H.1) (node x.1.1)) D L d r (r.symm ▸ (Nat.pow_le_pow_left hc 4)) (freshV (w:=p.width) G (by omega : p.width<Vδ) H.1 D f)
    unfold atZero at Hk; rw [norm_div] at Hk; rw [show qμ.moment W' P xβ Q'=_ from Hq]; exact (div_le_iff₀ hx).1 Hk
 have hv:= Ticket.combine qμ W' P xβ Q' (a.permit J) (t.permit J) (T_.bolt m R H) (T_.bolt _ A H) (T_.ruler R H _ v) (T_.ruler A H 3 rfl) (he ▸ hx) ha X' (by unfold Q' launchK; positivity) hy (show _ from (by rw [←he]; exact hα))
 unfold atZero; rw [← (at_m a z (Original.primary K) b), norm_div,←singleV T_ H R E b W' (rolls p z G T_ X H R v b W' H' w),show ‖partitionZ (C.warm m n 0) K.P (C.loom m 0)‖=_ from T_.price_scale R H]; -- tune
 apply le_trans hv; apply le_trans (mul_le_mul_of_nonneg_left ?_ hy.le) (show (e/8)*2≤ e/4 by linarith); apply (Real.le_log_iff_exp_le (by positivity)).1
 unfold Region.Ticket.lux at *; rw [←T_.price_scale H H, ←T_.price_scale A H]; exact le_trans (Eq.le (by unfold Region.Ticket.lux; ring : _ = Region.Ticket.lux 3 (barestar C K.q n) (barestar C (K.q*3) n) / (J.qcount o).val^4 * (3/2:ℝ)^4)) e'
end YM.CF.Buffered.Concert
#print axioms YM.CF.Buffered.Concert.showtime
