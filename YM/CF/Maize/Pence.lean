import YM.CF.Maize.Clay
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Maize
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Gloss Floe Ave Phase.Sample Jet Pastry Drapes
variable {H e p a d r k:ℝ}{n:ℕ}
private lemma vow_ct : Continuous (Floe.vow) := continuous_pi fun i => by unfold Floe.vow; split <;> fun_prop
lemma skin_CT: Continuous (skin (N:=N)):=by
 unfold skin; refine Continuous.prodMk (continuous_pi fun i=> ?_) (continuous_pi (fun i=>continuous_pi fun j=>?_))
 · let F(g:SU.E):=color SU.matter g; have hv:Continuous F:=by
    refine continuous_matrix fun i j=>?_ ; exact continuous_const.mul (SU.matter_cont.matrix_elem i.2 j.2) -- namespaces
   exact vow_ct.comp (hv.comp ((continuous_apply i).comp continuous_fst))
 exact vow_ct.comp (localPair_cont.comp ((continuous_apply _).comp ((continuous_apply _).comp continuous_snd)))
variable {s t:Tag (ku (N:=CSide m B) (a:=a))}{T:Stamp m B}
local notation "M" m B=> Elf m B
abbrev shines (e k:ℝ)(n:ℕ)(T: Train m B e→ Ewe m B)(H C:ℝ):=∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](V:E→Train m B e)(S:Set E), IsOpen S→(∀ i∈ S,V i∈Breath m B e)→Tagged e k n (release ∘ V) S → ∀ x∈ S, Allows n (fun x=>Gas.dilF H (T (V x))) x C
abbrev skim(Q:Dough (Hearth m B)):=Q
lemma ink (n:ℕ)(B:Side)(l:0<a)(b:1≤ k):∃ C:ℝ,0≤ C∧∀ (m:Side)(e:ℝ)(h:Room B e){A:Toll (Elf m B)}{X:Stamp m B}{V:Raw (Kelp (CSide m B) a) (Elf m B)}{s t:Tag (ku (a:=a) (N:=CSide m B))}, Suite (badge _) s t X A V→∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](f:E→Train m B e)(W:Set E),IsOpen W→Tagged e k n (release ∘ f) W→∀ x∈ W,∀ i j,Allows n (fun z=>cin m B (fun y=> V (uθ y l) i j) (f z)) x (C*A i j):=by
 obtain ⟨C,g,w⟩:=brimA n l b B; refine ⟨C,g,fun m e h A X V s t p E _ _ _ f W q p' x hx i j=>?_⟩
 let ht:=p.expo i j; let V₀:= release ∘ f; have hy:= p' x hx; have hv : stick (0:Row)∈Phase.zone {0}:=stick_in _ (mem_singleton_self _)
 exact w E m (fun y=>V y i j) (p.fuel i j) ht.connected (A i j) ht.bounded _ (fun z=> slot m (V₀ z).2) (stick 0) (stick 0) none x e {0} hv hv (by rw [sub_self,norm_zero]; positivity) h hy.2.1 (fun i=>hy.2.2 i.1) ((show ∀ᶠ y in 𝓝 x,y∈ W from q.mem_nhds hx).mono fun i k=> (p' i k).1) -- tune.cont name.F vars projection
-- combine
abbrev Κ(m B:Side)(a:ℝ):= Raw ↑(Kelp (CSide m B) a) (Elf m B)
def sailm(A C D: Κ m B a)(p:0<a)(x:Train m B e): Ewe m B:= town (m:=m) (B:=B) (e:=e) (fun d=> hang (n:=Elf m B) (A (uθ d p)) (C (uθ d p)) (D (uθ d p))) x
lemma shine_ink (n:ℕ)(B:Side)(l:0<a)(b:1≤ k):∃ C:ℝ,0≤ C ∧ ∀ (m:Side)(e:ℝ), Room B e→∀ (H:ℝ)(h:1≤ H){A F D: Κ m B a}{U V W: Toll (Elf m B)}{s t u v w z: Tag (ku (a:=a) (N:=CSide m B))}{P:Stamp m B},Suite (badge _) s t P U A→Suite (badge _) u v P V F→Suite (badge _) w z P W D→ shines e k n (sailm A F D l) H (C*(Linen.coins U V W* H^2)):=by
 obtain ⟨C,g,w⟩:=ink n B l b; refine ⟨C,g,fun m e h H t A F D U V W s z u y d k' S v hv Q E _ _ _ f X Y g' ht x p=>?_⟩ -- binders tune
 let T (t:Κ m B a)(x:E):Op (Elf m B):= fun i j=> cin m B (fun y=> t (uθ y l) i j) (f x); apply (perk_a (zero_le_one.trans t) (F:=T A) (A:=T F) (S:=T D) (w m e h v E f X Y ht x p) (w m e h hv E f X Y ht x p) (w m e h Q E f X Y ht x p)).germ
 filter_upwards [Y.mem_nhds p] with x g; change Gas.dilF H _ = Gas.dilF H _; apply congrArg; have hp:=tenant_t h (g' x g); simp_rw [sailm,town,T,cin, entrance (m:=m) (B:=B) (p:=stick 0) (q:=stick 0) (v:=none) hp]
end YM.CF.Maize
