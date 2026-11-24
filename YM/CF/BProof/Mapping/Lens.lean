import YM.CF.BProof.Mapping.Shadow

/- read linear map row permission from any Shade certificate. includes masked Tape for severe.
Heavy charged on short footprint mapping at Lens. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping.Pawn
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Charge House Gauss Release Release.hot Moment Push.AbsoluteSums Micro
open scoped Topology BigOperators Classical MatrixOrder Matrix
local notation "G"=> SU.group
variable {s c: Side}{Y:Yard s}(g:Ratio c s)(S:Hall s)(x y:Pawn Y)(Z: Finset (Block Y c))(z:ℝ)(T:PathData G){R:ℝ}{c':Clip}{M:ℕ}(θ:ℝ)(U: Beam c' R Y.short M z)(h:Room Y M)(u:Agreed g x y Z)
variable {r:ℕ} (a:Y.Col)(b:Y.Door)
abbrev weight := tape Y T θ U x.sev x.gauss
abbrev roof := roof_cost Y T θ z U x.sev x.gauss
include u
lemma horizon (B:Finset Y.Col→ Gauss.Pool (Roll.Stamp Y))(V:Prox.Via (edge Y) (Scope.flags _) B r)(p:Shade g Z a r)(i:Roll.Place Y): (B x.sev *ᵥ x.gauss) (a,i)=(B y.sev *ᵥ y.gauss) (a,i):=by
 refine sum_congr rfl fun j _=>?_; dsimp only; let K:=Gauss.base Y; by_cases t:(Gauss.base Y).N a j.1 r
 · rw [u.gauss j (p j.1 t)]; exact congrArg (·*y.gauss j) (V.lock (a,i) _ _ (fun j (v:j∈K.ball a r) => u.sev j (p j ((K.ball_m ..).1 v))) j)
 rw [V.door (a,i) j _ t,V.door (a,i) j _ t,zero_mul,zero_mul]
include h
lemma pin_h (p: Shade g Z a U.horizon') : pin Y T θ U x.sev x.gauss a=pin Y T θ U y.sev y.gauss a:= funext fun i=>horizon g x y Z u a _ (Beam.ζ_v T θ U h) p i
lemma weight_h (p:Shade g Z b.1 U.horizon'): weight x z T θ U b=weight y z T θ U b:= congrArg (fun w:Gauss.Via (Roll.Place Y)=> Pub.grant (CF.BProof.g z) (Pub.key («G»:=G) w b.2)) (pin_h g x y Z z T θ U h u _ p)
lemma roof_h (p:Shade g Z b.1 U.horizon') : Pawn.roof x z T θ U b=Pawn.roof y z T θ U b:= if_congr (u.sev _ (shade g Z _ _ p)) rfl (weight_h g x y Z z T θ U h u b p)
variable (l:Tile s)(p: Stove Y M l)
def rest := Lens Y l (M:=M)
omit h
lemma cave_h (p:Shade g Z (Lens Y l (M:=M)) (3*M)): Cave Y M l x.sev ↔ Cave Y M l y.sev:=forall_congr' fun i=> imp_congr_right fun v=> (u.sev i (p i (charge_close Y M l v))).not
lemma packs_h (p:Shade g Z (Lens Y l (M:=M)) (3*M)) : l∈ packs Y M x.sev a ↔ l∈ packs Y M y.sev a:=by
 have hx:Haz Y M l x.sev=Haz Y M l y.sev:=by ext i; simp only [Haz,mem_filter]; exact and_congr_left fun v=> u.sev _ (p i (charge_close Y M l v))
 simp only [packs,mem_filter,bail,hx, cave_h g x y Z u l p] -- tune
include h p
lemma linear_h (v:Shade g Z (Lens Y l (M:=M)) (3*M+U.horizon')) : Form.linear T M l (Y.roll (Pawn.roof x z T θ U))=Form.linear T M l (Y.roll (Pawn.roof y z T θ U)):= cave_dep Y M l h _ p T _ (fun b q=> roof_h g x y Z z T θ U h u b (shade_rides g Z v (charge_close _ _ _ q)))
variable (q:BudgetPoint){β w v':ℝ}(t:T.Bounds c' w R v')(k:ValidR c' q M)(hx:Certified S x z T θ U)(hy:Certified S y z T θ U)
include t k hx hy
lemma heavy_h (H: 5*M+2<2*Deep.D Y)(v:Shade g Z (Lens Y l (M:=M)) (3*M+U.horizon')) : heavy c' q T M β (put S x z T θ U) l=heavy c' q T M β (put S y z T θ U) l:=by
 apply touch_local l q c' T β t k; intro b g₁ g₂; apply detect g S x y Z z T θ U h u hx hy (pilot l) (blamed Y M l p) (k:=M+2) (by omega) b (bounded M l g₁) (fun i p=> v i ((Gauss.base _).mono ?_ p)); have := h.seed; omega
lemma taylor_h (H:5*M+2<2*Deep.D Y)(v:Shade g Z (Lens Y l (M:=M)) (3*M+U.horizon')) : Form.Taylor z (Y.roll (Pawn.roof x z T θ U)) c' q T M (put S x z T θ U) β l= Form.Taylor z (Y.roll (Pawn.roof y z T θ U)) c' q T M (put S y z T θ U) β l:=by unfold Form.Taylor Form.L Form.Q; rw [linear_h g x y Z z T θ U h u l p v,heavy_h g S x y Z z T θ U h u l p q t k hx hy H v]
-- packs reach from assigned severe. guardian cost reads no x/y mismatch from out-of-horizon selection.
omit p
lemma strong_h (H: 5*M+2<2*Deep.D Y)(v:Shade g Z a (6*M+U.horizon')) : strong Y M x.sev z c' q T β (put S x z T θ U) (Pawn.roof x z T θ U) a=strong Y M y.sev z c' q T β (put S y z T θ U) (Pawn.roof y z T θ U) a:=by
 unfold strong packs; simp_rw [sum_filter]; refine sum_congr rfl fun i _=>?_ ; by_cases hv:i∈ Gear Y M a
 · obtain ⟨hG,hb⟩:=(engaged ..).1 hv; have he:Shade g Z (Lens Y i (M:=M)) (3*M+U.horizon'):= by refine shade_rides g Z ?_ ((Gauss.base Y).symm (charge_close _ _ _ hb)); convert v using 1; omega
   let e(x:Pawn Y):= Form.sound z c' q T M β i +Form.L T M c' β z i (Y.roll (Pawn.roof x z T θ U))-heavy c' q T M β (put S x z T θ U) i
   apply if_congr; · simpa only [packs,mem_filter,mem_univ,true_and] using packs_h g x y Z u a i (fun i q=> he i ((Gauss.base Y).mono (by omega) q)) -- tune
   · rw [Form.L,Form.L,linear_h g x y Z z T θ U h u i hG he,heavy_h g S x y Z z T θ U h u i hG q t k hx hy H he]
   exact rfl
 rw [if_neg,if_neg] <;> exact fun H=>hv (pack_v Y M _ _ (mem_filter.mpr ⟨mem_univ _,H⟩))
end YM.CF.BProof.Mapping.Pawn
