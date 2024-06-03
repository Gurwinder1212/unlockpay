function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}
function null_to_empty(value) {
    return value == null ? '' : value;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link0;
	let link1;
	let link2;
	let link3;
	let script0;
	let script0_src_value;
	let script1;
	let script1_src_value;
	let link4;
	let link4_href_value;
	let meta2;
	let meta3;
	let meta4;
	let meta5;
	let meta6;
	let style;
	let t;

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link0 = element("link");
			link1 = element("link");
			link2 = element("link");
			link3 = element("link");
			script0 = element("script");
			script1 = element("script");
			link4 = element("link");
			meta2 = element("meta");
			meta3 = element("meta");
			meta4 = element("meta");
			meta5 = element("meta");
			meta6 = element("meta");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\n:root {\n  /* Fonts  */\n  --font-heading: 'Fraunces', serif;\n  --font-body: 'IBM Plex Mono', monospace;\n  --font-text: 'Work Sans', sans-serif;\n  \n  /* Colors */\n  --color-Y500: #E9D90A;\n  --color-Y400: #F6E500;\n  --color-Y300: #F7D254;\n  --color-Y200: #FFF587;\n  --color-Y100: #FFFCDA;\n\n  --color-P500: #E82884;\n  --color-P400: #FF4FA3;\n  --color-P300: #FF74B7;\n  --color-P200: #FFB1D7;\n  --color-P100: #FFD6E9;\n\n  --color-T500: #50ADBE;\n  --color-T400: #69C9DB;\n  --color-T300: #A8E1EC;\n  --color-T200: #C2F1FA;\n  --color-T100: #E2FAFF;\n\n  --color-G500: #C8C9DC;\n  --color-G400: #D5D7EF;\n  --color-G300: #E6E7FB;\n  --color-G200: #EEF2FD;\n  --color-G100: #F4F9FC;\n\n  --color-black: #000000;\n  --color-white: #FFFFFF;\n  \n  /* Base values */\n  --color-primary: var(--color-Y400);\n  --color-secondary: var(--color-P400);\n  --color-tertiary: var(--color-black);\n  --color-tertiary: var(--color-white);\n  \n  /* --color: var(--color-base);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #eee;\n  --background: white; */\n  --border: 0.851905px solid var(--color-black);\n  --border-radius: 4.25952px;\n  --max-content-width-mobile: 768px;\n  --max-content-width-small-desktop: 900px;\n  --max-content-width: 1200px;\n  --page-padding-desktop: 90px 80px;\n  --page-padding-small-desktop: 120px 60px;\n  --page-padding-mobile: 90px 18px;\n\n  --hero-padding-desktop: 150px 80px 90px 80px;\n  --hero-padding-large-desktop: 200px 80px 90px 80px;\n\n  --hero-padding-mobile: 100px 18px 90px 18px;\n  --content-padding: 0px 50px;\n  \n}\n\n\n#page a {\n    color: var(--color-black);\n  }\n\n\n#page h1,#page h2,#page h3,#page h4 {\n    font-family: var(--font-heading);\n    font-weight: 700;\n    color: var(--color-black);\n  }\n\n\n#page h1 {\n    font-size: 33px;\n    line-height: 39px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h1 {\n      font-size:  67px;\n      line-height: 69px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h1 {\n      font-size:  83px;\n      line-height: 93px\n  }\n    }\n\n\n#page h2 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h2 {\n      font-size:  55px;\n      line-height: 65px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h2 {\n      font-size:  65px;\n      line-height: 75px\n  }\n    }\n\n\n#page h3 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h3 {\n      font-size:  45px;\n      line-height: 57px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h3 {\n      font-size:  55px;\n      line-height: 68px\n  }\n    }\n\n\n#page h4 {\n    font-size: 26px;\n    line-height: 34px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h4 {\n      font-size:  37px;\n      line-height: 50px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h4 {\n      font-size:  45px;\n      line-height: 58px\n  }\n    }\n\n\n#page h5, #page h6, #page .h650, #page .h700, #page .h800, #page .h900, #page .h950 {\n    font-family: var(--font-body);\n    color: var(--color-black);\n  }\n\n\n#page h5 {\n    font-weight: 700;\n    font-size: 20px;\n    line-height: 28px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n#page h6 {\n    font-weight: 700;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h6 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h6 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h650 {\n    font-weight: 500;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h650 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h650 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h700 {\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h700 {\n      font-size:  16px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h700 {\n      font-size:  18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .h800 {\n    font-weight: 500;\n    font-size: 12px;\n    line-height: 16px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h800 {\n      font-size:  12px;\n      line-height: 16px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h800 {\n      font-size:  17px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h900 {\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h900 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h900 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h950 {\n    font-weight: 500;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h950 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h950 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page p {\n    font-family: var(--font-text);\n    font-weight: 400;\n    color: var(--color-black);\n  }\n\n\n#page .p-large {\n    font-size: 17px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-large {\n      font-size:  18px;\n      line-height: 28px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-large {\n      font-size:  20px;\n      line-height: 31px\n  }\n    }\n\n\n#page .p-medium {\n    font-size: 15px;\n    line-height: 22px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-medium {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-medium {\n      font-size:  17px;\n      line-height: 25px\n  }\n    }\n\n\n#page .p-small {\n    font-size: 13px;\n    line-height: 18px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-small {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-small {\n      font-size:  14px;\n      line-height: 18px\n  }\n    }\n\n\n#page .link {\n    color: var(--color-P500);\n    -webkit-text-decoration-line: underline;\n            text-decoration-line: underline;\n  }\n\n\n#page .link:hover {\n      -webkit-text-decoration-line: unset;\n              text-decoration-line: unset;\n    }\n\n\n#page .link:active {\n      color: var(--color-P300);\n    }\n\n\n#page .link:visited {\n      color: var(--color-P500);\n      -webkit-text-decoration-line: underline;\n              text-decoration-line: underline;\n    }\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 12.7786px;\n    gap: 8.52px;\n    height: 34.52px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n      height: 41.52px\n  }\n    }\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 10px;\n    gap: 8.52px;\n    height: 32px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n      height: 37px\n  }\n    }\n\n\n#page .tag-pink-large {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-pink-small {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-yellow-large {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-yellow-small {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-lightyellow-large {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .tag-lightyellow-small {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .primary-large-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 60px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 20px 35px;\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 23px;\n    border: 2px solid var(--color-black);\n    transition: all 0.5s;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-large-button {\n      padding: 25px 40px;\n      font-weight: 700;\n      font-size: 18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .primary-large-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-large-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .primary-small-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 40px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 10px 25px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n    transition: all 0.5s;\n    border: 2px solid var(--color-black);\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-small-button {\n      padding: 15px 40px;\n      font-weight: 700;\n      font-size: 16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .primary-small-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-small-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .secondary-button {\n    font-family: var(--font-body); \n    color: var(--color-black);\n    border-radius: 100px;\n    height: 52px;\n    border: 3px solid var(--color-black);\n    color: var(--color-black);\n    transition: all 0.5s;\n    padding: 15px 34px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 22px;\n    background: transparent;\n  }\n\n\n#page .secondary-button:hover {\n      background: var(--color-black);\n      color: var(--color-white);\n    }\n\n\n#page .secondary-button:active {\n      background: var(--color-G500);\n      border-color: var(--color-G500);\n    }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1mk00iu', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link0 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true, crossorigin: true });
			link2 = claim_element(head_nodes, "LINK", { href: true, rel: true });
			link3 = claim_element(head_nodes, "LINK", { rel: true, type: true, href: true });
			script0 = claim_element(head_nodes, "SCRIPT", { type: true, src: true });
			var script0_nodes = children(script0);
			script0_nodes.forEach(detach);
			script1 = claim_element(head_nodes, "SCRIPT", { src: true });
			var script1_nodes = children(script1);
			script1_nodes.forEach(detach);

			link4 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			meta2 = claim_element(head_nodes, "META", { charset: true });
			meta3 = claim_element(head_nodes, "META", { name: true, content: true });
			meta4 = claim_element(head_nodes, "META", { name: true, content: true });
			meta5 = claim_element(head_nodes, "META", { name: true, content: true });
			meta6 = claim_element(head_nodes, "META", { name: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\n:root {\n  /* Fonts  */\n  --font-heading: 'Fraunces', serif;\n  --font-body: 'IBM Plex Mono', monospace;\n  --font-text: 'Work Sans', sans-serif;\n  \n  /* Colors */\n  --color-Y500: #E9D90A;\n  --color-Y400: #F6E500;\n  --color-Y300: #F7D254;\n  --color-Y200: #FFF587;\n  --color-Y100: #FFFCDA;\n\n  --color-P500: #E82884;\n  --color-P400: #FF4FA3;\n  --color-P300: #FF74B7;\n  --color-P200: #FFB1D7;\n  --color-P100: #FFD6E9;\n\n  --color-T500: #50ADBE;\n  --color-T400: #69C9DB;\n  --color-T300: #A8E1EC;\n  --color-T200: #C2F1FA;\n  --color-T100: #E2FAFF;\n\n  --color-G500: #C8C9DC;\n  --color-G400: #D5D7EF;\n  --color-G300: #E6E7FB;\n  --color-G200: #EEF2FD;\n  --color-G100: #F4F9FC;\n\n  --color-black: #000000;\n  --color-white: #FFFFFF;\n  \n  /* Base values */\n  --color-primary: var(--color-Y400);\n  --color-secondary: var(--color-P400);\n  --color-tertiary: var(--color-black);\n  --color-tertiary: var(--color-white);\n  \n  /* --color: var(--color-base);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #eee;\n  --background: white; */\n  --border: 0.851905px solid var(--color-black);\n  --border-radius: 4.25952px;\n  --max-content-width-mobile: 768px;\n  --max-content-width-small-desktop: 900px;\n  --max-content-width: 1200px;\n  --page-padding-desktop: 90px 80px;\n  --page-padding-small-desktop: 120px 60px;\n  --page-padding-mobile: 90px 18px;\n\n  --hero-padding-desktop: 150px 80px 90px 80px;\n  --hero-padding-large-desktop: 200px 80px 90px 80px;\n\n  --hero-padding-mobile: 100px 18px 90px 18px;\n  --content-padding: 0px 50px;\n  \n}\n\n\n#page a {\n    color: var(--color-black);\n  }\n\n\n#page h1,#page h2,#page h3,#page h4 {\n    font-family: var(--font-heading);\n    font-weight: 700;\n    color: var(--color-black);\n  }\n\n\n#page h1 {\n    font-size: 33px;\n    line-height: 39px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h1 {\n      font-size:  67px;\n      line-height: 69px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h1 {\n      font-size:  83px;\n      line-height: 93px\n  }\n    }\n\n\n#page h2 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h2 {\n      font-size:  55px;\n      line-height: 65px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h2 {\n      font-size:  65px;\n      line-height: 75px\n  }\n    }\n\n\n#page h3 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h3 {\n      font-size:  45px;\n      line-height: 57px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h3 {\n      font-size:  55px;\n      line-height: 68px\n  }\n    }\n\n\n#page h4 {\n    font-size: 26px;\n    line-height: 34px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h4 {\n      font-size:  37px;\n      line-height: 50px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h4 {\n      font-size:  45px;\n      line-height: 58px\n  }\n    }\n\n\n#page h5, #page h6, #page .h650, #page .h700, #page .h800, #page .h900, #page .h950 {\n    font-family: var(--font-body);\n    color: var(--color-black);\n  }\n\n\n#page h5 {\n    font-weight: 700;\n    font-size: 20px;\n    line-height: 28px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n#page h6 {\n    font-weight: 700;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h6 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h6 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h650 {\n    font-weight: 500;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h650 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h650 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h700 {\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h700 {\n      font-size:  16px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h700 {\n      font-size:  18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .h800 {\n    font-weight: 500;\n    font-size: 12px;\n    line-height: 16px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h800 {\n      font-size:  12px;\n      line-height: 16px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h800 {\n      font-size:  17px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h900 {\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h900 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h900 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h950 {\n    font-weight: 500;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h950 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h950 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page p {\n    font-family: var(--font-text);\n    font-weight: 400;\n    color: var(--color-black);\n  }\n\n\n#page .p-large {\n    font-size: 17px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-large {\n      font-size:  18px;\n      line-height: 28px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-large {\n      font-size:  20px;\n      line-height: 31px\n  }\n    }\n\n\n#page .p-medium {\n    font-size: 15px;\n    line-height: 22px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-medium {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-medium {\n      font-size:  17px;\n      line-height: 25px\n  }\n    }\n\n\n#page .p-small {\n    font-size: 13px;\n    line-height: 18px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-small {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-small {\n      font-size:  14px;\n      line-height: 18px\n  }\n    }\n\n\n#page .link {\n    color: var(--color-P500);\n    -webkit-text-decoration-line: underline;\n            text-decoration-line: underline;\n  }\n\n\n#page .link:hover {\n      -webkit-text-decoration-line: unset;\n              text-decoration-line: unset;\n    }\n\n\n#page .link:active {\n      color: var(--color-P300);\n    }\n\n\n#page .link:visited {\n      color: var(--color-P500);\n      -webkit-text-decoration-line: underline;\n              text-decoration-line: underline;\n    }\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 12.7786px;\n    gap: 8.52px;\n    height: 34.52px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n      height: 41.52px\n  }\n    }\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 10px;\n    gap: 8.52px;\n    height: 32px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n      height: 37px\n  }\n    }\n\n\n#page .tag-pink-large {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-pink-small {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-yellow-large {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-yellow-small {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-lightyellow-large {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .tag-lightyellow-small {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .primary-large-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 60px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 20px 35px;\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 23px;\n    border: 2px solid var(--color-black);\n    transition: all 0.5s;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-large-button {\n      padding: 25px 40px;\n      font-weight: 700;\n      font-size: 18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .primary-large-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-large-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .primary-small-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 40px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 10px 25px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n    transition: all 0.5s;\n    border: 2px solid var(--color-black);\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-small-button {\n      padding: 15px 40px;\n      font-weight: 700;\n      font-size: 16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .primary-small-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-small-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .secondary-button {\n    font-family: var(--font-body); \n    color: var(--color-black);\n    border-radius: 100px;\n    height: 52px;\n    border: 3px solid var(--color-black);\n    color: var(--color-black);\n    transition: all 0.5s;\n    padding: 15px 34px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 22px;\n    background: transparent;\n  }\n\n\n#page .secondary-button:hover {\n      background: var(--color-black);\n      color: var(--color-white);\n    }\n\n\n#page .secondary-button:active {\n      background: var(--color-G500);\n      border-color: var(--color-G500);\n    }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link0, "rel", "preconnect");
			attr(link0, "href", "https://fonts.googleapis.com");
			attr(link1, "rel", "preconnect");
			attr(link1, "href", "https://fonts.gstatic.com");
			attr(link1, "crossorigin", "");
			attr(link2, "href", "https://fonts.googleapis.com/css2?family=Fraunces:wght@700&family=IBM+Plex+Mono:wght@500;700&family=Work+Sans&display=swap");
			attr(link2, "rel", "stylesheet");
			attr(link3, "rel", "stylesheet");
			attr(link3, "type", "text/css");
			attr(link3, "href", "https://cdn.jsdelivr.net/npm/toastify-js/src/toastify.min.css");
			attr(script0, "type", "text/javascript");
			if (!src_url_equal(script0.src, script0_src_value = "https://cdn.jsdelivr.net/npm/toastify-js")) attr(script0, "src", script0_src_value);
			if (!src_url_equal(script1.src, script1_src_value = "https://unpkg.com/@lottiefiles/lottie-player@1.5.7/dist/lottie-player.js")) attr(script1, "src", script1_src_value);
			attr(link4, "rel", "icon");
			attr(link4, "type", "image/png");
			attr(link4, "sizes", "32x32");
			attr(link4, "href", link4_href_value = /*favicon*/ ctx[0].url);
			document.title = "UNLOK Loyalty | Privacy";
			attr(meta2, "charset", "UTF-8");
			attr(meta3, "name", "description");
			attr(meta3, "content", "Unleash the Power of Blockchain Rewards");
			attr(meta4, "name", "keywords");
			attr(meta4, "content", "Blockchain, Crypto, Cryptocurrency, Unlok, Rewards, Staking, Loyalty Program, Earn, Redeem");
			attr(meta5, "name", "author");
			attr(meta5, "content", "Unlok Loyalty");
			attr(meta6, "name", "viewport");
			attr(meta6, "content", "width=device-width, initial-scale=1.0");
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, link2);
			append_hydration(document.head, link3);
			append_hydration(document.head, script0);
			append_hydration(document.head, script1);
			append_hydration(document.head, link4);
			append_hydration(document.head, meta2);
			append_hydration(document.head, meta3);
			append_hydration(document.head, meta4);
			append_hydration(document.head, meta5);
			append_hydration(document.head, meta6);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 1 && link4_href_value !== (link4_href_value = /*favicon*/ ctx[0].url)) {
				attr(link4, "href", link4_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link0);
			detach(link1);
			detach(link2);
			detach(link3);
			detach(script0);
			detach(script1);
			detach(link4);
			detach(meta2);
			detach(meta3);
			detach(meta4);
			detach(meta5);
			detach(meta6);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { favicon: 0 });
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

// (254:35) 
function create_if_block_4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			attr(img, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (252:10) {#if logo.title}
function create_if_block_3(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (259:10) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let h6;
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_class_value;
	let a_href_value;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { class: true });
			var h6_nodes = children(h6);
			a = claim_element(h6_nodes, "A", { id: true, class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "id", "nav-item");

			attr(a, "class", a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"));

			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(h6, "class", "h950");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_class_value !== (a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"))) {
				attr(a, "class", a_class_value);
			}

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

// (273:35) 
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			attr(img, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (271:10) {#if logo.title}
function create_if_block_1$1(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (289:8) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t0;
	let a;
	let t1_value = /*site_nav_button*/ ctx[2].label + "";
	let t1;
	let a_href_value;
	let t2;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			a = element("a");
			t1 = text(t1_value);
			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t0 = claim_space(nav_nodes);
			a = claim_element(nav_nodes, "A", { class: true, id: true, href: true });
			var a_nodes = children(a);
			t1 = claim_text(a_nodes, t1_value);
			a_nodes.forEach(detach);
			t2 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "primary-small-button");
			attr(a, "id", "nav");
			attr(a, "href", a_href_value = /*site_nav_button*/ ctx[2].url);
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-jc1u8d");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t0);
			append_hydration(nav, a);
			append_hydration(a, t1);
			append_hydration(nav, t2);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[7]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*window, site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t0);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if ((!current || dirty & /*site_nav_button*/ 4) && t1_value !== (t1_value = /*site_nav_button*/ ctx[2].label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*site_nav_button*/ 4 && a_href_value !== (a_href_value = /*site_nav_button*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (292:14) {#each site_nav as { link }}
function create_each_block(ctx) {
	let h6;
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_class_value;
	let a_href_value;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { class: true });
			var h6_nodes = children(h6);

			a = claim_element(h6_nodes, "A", {
				id: true,
				class: true,
				active: true,
				href: true
			});

			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "id", "nav-item");

			attr(a, "class", a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"));

			attr(a, "active", "true");
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(h6, "class", "h950");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_class_value !== (a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"))) {
				attr(a, "class", a_class_value);
			}

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

function create_fragment$2(ctx) {
	let div4;
	let header;
	let div3;
	let div2;
	let div0;
	let a0;
	let t0;
	let nav;
	let t1;
	let a1;
	let t2_value = /*site_nav_button*/ ctx[2].label + "";
	let t2;
	let a1_href_value;
	let t3;
	let div1;
	let a2;
	let t4;
	let button;
	let icon;
	let t5;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_3;
		if (/*logo*/ ctx[0].image.url) return create_if_block_4;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type && current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_1$1;
		if (/*logo*/ ctx[0].image.url) return create_if_block_2;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1 && current_block_type_1(ctx);

	icon = new Component$1({
			props: {
				height: "37",
				icon: "eva:menu-outline",
				style: "color:black;"
			}
		});

	let if_block2 = /*mobileNavOpen*/ ctx[3] && create_if_block$1(ctx);

	return {
		c() {
			div4 = element("div");
			header = element("header");
			div3 = element("div");
			div2 = element("div");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			a1 = element("a");
			t2 = text(t2_value);
			t3 = space();
			div1 = element("div");
			a2 = element("a");
			if (if_block1) if_block1.c();
			t4 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t5 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			header = claim_element(div4_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div3 = claim_element(header_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { style: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);
			a1 = claim_element(nav_nodes, "A", { class: true, id: true, href: true });
			var a1_nodes = children(a1);
			t2 = claim_text(a1_nodes, t2_value);
			a1_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a2 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a2_nodes = children(a2);
			if (if_block1) if_block1.l(a2_nodes);
			a2_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t5 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-jc1u8d");
			attr(a1, "class", "primary-small-button");
			attr(a1, "id", "nav");
			attr(a1, "href", a1_href_value = /*site_nav_button*/ ctx[2].url);
			set_style(nav, "display", "flex");
			set_style(nav, "align-items", "center");
			attr(nav, "class", "svelte-jc1u8d");
			attr(div0, "class", "desktop-nav svelte-jc1u8d");
			attr(a2, "href", "/");
			attr(a2, "class", "logo svelte-jc1u8d");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-jc1u8d");
			attr(div2, "class", "section-container svelte-jc1u8d");
			attr(div3, "class", "header-container svelte-jc1u8d");
			attr(header, "class", "svelte-jc1u8d");
			attr(div4, "class", "section");
			attr(div4, "id", "section-a0d9ae12");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, header);
			append_hydration(header, div3);
			append_hydration(div3, div2);
			append_hydration(div2, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);
			append_hydration(nav, a1);
			append_hydration(a1, t2);
			append_hydration(div2, t3);
			append_hydration(div2, div1);
			append_hydration(div1, a2);
			if (if_block1) if_block1.m(a2, null);
			append_hydration(div1, t4);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t5);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if (if_block0) if_block0.d(1);
				if_block0 = current_block_type && current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*window, site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t1);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if ((!current || dirty & /*site_nav_button*/ 4) && t2_value !== (t2_value = /*site_nav_button*/ ctx[2].label + "")) set_data(t2, t2_value);

			if (!current || dirty & /*site_nav_button*/ 4 && a1_href_value !== (a1_href_value = /*site_nav_button*/ ctx[2].url)) {
				attr(a1, "href", a1_href_value);
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if (if_block1) if_block1.d(1);
				if_block1 = current_block_type_1 && current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a2, null);
				}
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$1(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);

			if (if_block0) {
				if_block0.d();
			}

			destroy_each(each_blocks, detaching);

			if (if_block1) {
				if_block1.d();
			}

			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { site_nav_button } = $$props;
	let mobileNavOpen = false;

	function toggleMobileNav() {
		$$invalidate(3, mobileNavOpen = !mobileNavOpen);

		if (mobileNavOpen) {
			document.body.style.overflow = 'hidden';
		} else {
			document.body.style.overflow = 'unset';
		}
	}

	const click_handler = () => toggleMobileNav();
	const click_handler_1 = () => toggleMobileNav();

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('site_nav_button' in $$props) $$invalidate(2, site_nav_button = $$props.site_nav_button);
	};

	return [
		logo,
		site_nav,
		site_nav_button,
		mobileNavOpen,
		toggleMobileNav,
		favicon,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			favicon: 5,
			logo: 0,
			site_nav: 1,
			site_nav_button: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$3(ctx) {
	let div2;
	let div1;
	let div0;
	let h1;
	let t0;
	let t1;
	let h6;
	let t2;
	let t3;
	let p;
	let t4;

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			h1 = element("h1");
			t0 = text(/*hero_title_1*/ ctx[0]);
			t1 = space();
			h6 = element("h6");
			t2 = text(/*hero_title_2*/ ctx[1]);
			t3 = space();
			p = element("p");
			t4 = text(/*hero_description*/ ctx[2]);
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h1 = claim_element(div0_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, /*hero_title_1*/ ctx[0]);
			h1_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h6 = claim_element(div0_nodes, "H6", { class: true });
			var h6_nodes = children(h6);
			t2 = claim_text(h6_nodes, /*hero_title_2*/ ctx[1]);
			h6_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			p = claim_element(div0_nodes, "P", { class: true });
			var p_nodes = children(p);
			t4 = claim_text(p_nodes, /*hero_description*/ ctx[2]);
			p_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "svelte-nv92w4");
			attr(h6, "class", "h700 svelte-nv92w4");
			attr(p, "class", "p-large svelte-nv92w4");
			attr(div0, "class", "hero-wrapper svelte-nv92w4");
			attr(div1, "class", "hero-container svelte-nv92w4");
			attr(div2, "class", "section");
			attr(div2, "id", "section-460c1552");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			append_hydration(div0, h1);
			append_hydration(h1, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h6);
			append_hydration(h6, t2);
			append_hydration(div0, t3);
			append_hydration(div0, p);
			append_hydration(p, t4);
		},
		p(ctx, [dirty]) {
			if (dirty & /*hero_title_1*/ 1) set_data(t0, /*hero_title_1*/ ctx[0]);
			if (dirty & /*hero_title_2*/ 2) set_data(t2, /*hero_title_2*/ ctx[1]);
			if (dirty & /*hero_description*/ 4) set_data(t4, /*hero_description*/ ctx[2]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { site_nav_button } = $$props;
	let { hero_title_1 } = $$props;
	let { hero_title_2 } = $$props;
	let { hero_description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('logo' in $$props) $$invalidate(4, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(5, site_nav = $$props.site_nav);
		if ('site_nav_button' in $$props) $$invalidate(6, site_nav_button = $$props.site_nav_button);
		if ('hero_title_1' in $$props) $$invalidate(0, hero_title_1 = $$props.hero_title_1);
		if ('hero_title_2' in $$props) $$invalidate(1, hero_title_2 = $$props.hero_title_2);
		if ('hero_description' in $$props) $$invalidate(2, hero_description = $$props.hero_description);
	};

	return [
		hero_title_1,
		hero_title_2,
		hero_description,
		favicon,
		logo,
		site_nav,
		site_nav_button
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 3,
			logo: 4,
			site_nav: 5,
			site_nav_button: 6,
			hero_title_1: 0,
			hero_title_2: 1,
			hero_description: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$4(ctx) {
	let div1;
	let div0;
	let ol;
	let section0;
	let h60;
	let t0;
	let t1_value = /*bullet_1*/ ctx[0].title + "";
	let t1;
	let t2;
	let ul0;
	let li0;
	let t3;
	let t4_value = /*bullet_1*/ ctx[0].a + "";
	let t4;
	let t5;
	let li1;
	let t6;
	let t7_value = /*bullet_1*/ ctx[0].b + "";
	let t7;
	let t8;
	let li2;
	let t9;
	let t10_value = /*bullet_1*/ ctx[0].c + "";
	let t10;
	let t11;
	let section1;
	let h61;
	let t12;
	let t13_value = /*bullet_2*/ ctx[1].title + "";
	let t13;
	let t14;
	let ul1;
	let li3;
	let t15;
	let t16_value = /*bullet_2*/ ctx[1].a + "";
	let t16;
	let t17;
	let li4;
	let t18;
	let t19_value = /*bullet_2*/ ctx[1].b + "";
	let t19;
	let t20;
	let li5;
	let t21;
	let t22_value = /*bullet_2*/ ctx[1].c + "";
	let t22;
	let t23;
	let li6;
	let t24;
	let t25_value = /*bullet_2*/ ctx[1].d + "";
	let t25;
	let t26;
	let section2;
	let h62;
	let t27;
	let t28_value = /*bullet_3*/ ctx[2].title + "";
	let t28;
	let t29;
	let ul2;
	let li7;
	let t30;
	let t31_value = /*bullet_3*/ ctx[2].a + "";
	let t31;
	let t32;
	let li8;
	let t33;
	let t34_value = /*bullet_3*/ ctx[2].b + "";
	let t34;
	let t35;
	let section3;
	let h63;
	let t36;
	let t37_value = /*bullet_4*/ ctx[3].title + "";
	let t37;
	let t38;
	let ul3;
	let li9;
	let t39;
	let t40_value = /*bullet_4*/ ctx[3].a + "";
	let t40;
	let t41;
	let li10;
	let t42;
	let t43_value = /*bullet_4*/ ctx[3].b + "";
	let t43;
	let t44;
	let section4;
	let h64;
	let t45;
	let t46_value = /*bullet_5*/ ctx[4].title + "";
	let t46;
	let t47;
	let ul4;
	let li11;
	let t48;
	let t49_value = /*bullet_5*/ ctx[4].a + "";
	let t49;
	let t50;
	let li12;
	let t51;
	let t52_value = /*bullet_5*/ ctx[4].b + "";
	let t52;
	let t53;
	let section5;
	let h65;
	let t54;
	let t55_value = /*bullet_6*/ ctx[5].title + "";
	let t55;
	let t56;
	let ul5;
	let li13;
	let t57;
	let t58_value = /*bullet_6*/ ctx[5].a + "";
	let t58;
	let t59;
	let section6;
	let h66;
	let t60;
	let t61_value = /*bullet_7*/ ctx[6].title + "";
	let t61;
	let t62;
	let ul6;
	let li14;
	let t63;
	let t64_value = /*bullet_7*/ ctx[6].a + "";
	let t64;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			ol = element("ol");
			section0 = element("section");
			h60 = element("h6");
			t0 = text("1. ");
			t1 = text(t1_value);
			t2 = space();
			ul0 = element("ul");
			li0 = element("li");
			t3 = text("a. ");
			t4 = text(t4_value);
			t5 = space();
			li1 = element("li");
			t6 = text("b. ");
			t7 = text(t7_value);
			t8 = space();
			li2 = element("li");
			t9 = text("c. ");
			t10 = text(t10_value);
			t11 = space();
			section1 = element("section");
			h61 = element("h6");
			t12 = text("2. ");
			t13 = text(t13_value);
			t14 = space();
			ul1 = element("ul");
			li3 = element("li");
			t15 = text("a. ");
			t16 = text(t16_value);
			t17 = space();
			li4 = element("li");
			t18 = text("b. ");
			t19 = text(t19_value);
			t20 = space();
			li5 = element("li");
			t21 = text("c. ");
			t22 = text(t22_value);
			t23 = space();
			li6 = element("li");
			t24 = text("d. ");
			t25 = text(t25_value);
			t26 = space();
			section2 = element("section");
			h62 = element("h6");
			t27 = text("3. ");
			t28 = text(t28_value);
			t29 = space();
			ul2 = element("ul");
			li7 = element("li");
			t30 = text("a. ");
			t31 = text(t31_value);
			t32 = space();
			li8 = element("li");
			t33 = text("b. ");
			t34 = text(t34_value);
			t35 = space();
			section3 = element("section");
			h63 = element("h6");
			t36 = text("4. ");
			t37 = text(t37_value);
			t38 = space();
			ul3 = element("ul");
			li9 = element("li");
			t39 = text("a. ");
			t40 = text(t40_value);
			t41 = space();
			li10 = element("li");
			t42 = text("b. ");
			t43 = text(t43_value);
			t44 = space();
			section4 = element("section");
			h64 = element("h6");
			t45 = text("5. ");
			t46 = text(t46_value);
			t47 = space();
			ul4 = element("ul");
			li11 = element("li");
			t48 = text("a. ");
			t49 = text(t49_value);
			t50 = space();
			li12 = element("li");
			t51 = text("b. ");
			t52 = text(t52_value);
			t53 = space();
			section5 = element("section");
			h65 = element("h6");
			t54 = text("6. ");
			t55 = text(t55_value);
			t56 = space();
			ul5 = element("ul");
			li13 = element("li");
			t57 = text("a. ");
			t58 = text(t58_value);
			t59 = space();
			section6 = element("section");
			h66 = element("h6");
			t60 = text("7. ");
			t61 = text(t61_value);
			t62 = space();
			ul6 = element("ul");
			li14 = element("li");
			t63 = text("a. ");
			t64 = text(t64_value);
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			ol = claim_element(div0_nodes, "OL", {});
			var ol_nodes = children(ol);
			section0 = claim_element(ol_nodes, "SECTION", { id: true });
			var section0_nodes = children(section0);
			h60 = claim_element(section0_nodes, "H6", { class: true });
			var h60_nodes = children(h60);
			t0 = claim_text(h60_nodes, "1. ");
			t1 = claim_text(h60_nodes, t1_value);
			h60_nodes.forEach(detach);
			t2 = claim_space(section0_nodes);
			ul0 = claim_element(section0_nodes, "UL", {});
			var ul0_nodes = children(ul0);
			li0 = claim_element(ul0_nodes, "LI", { class: true });
			var li0_nodes = children(li0);
			t3 = claim_text(li0_nodes, "a. ");
			t4 = claim_text(li0_nodes, t4_value);
			li0_nodes.forEach(detach);
			t5 = claim_space(ul0_nodes);
			li1 = claim_element(ul0_nodes, "LI", { class: true });
			var li1_nodes = children(li1);
			t6 = claim_text(li1_nodes, "b. ");
			t7 = claim_text(li1_nodes, t7_value);
			li1_nodes.forEach(detach);
			t8 = claim_space(ul0_nodes);
			li2 = claim_element(ul0_nodes, "LI", { class: true });
			var li2_nodes = children(li2);
			t9 = claim_text(li2_nodes, "c. ");
			t10 = claim_text(li2_nodes, t10_value);
			li2_nodes.forEach(detach);
			ul0_nodes.forEach(detach);
			section0_nodes.forEach(detach);
			t11 = claim_space(ol_nodes);
			section1 = claim_element(ol_nodes, "SECTION", { id: true });
			var section1_nodes = children(section1);
			h61 = claim_element(section1_nodes, "H6", { class: true });
			var h61_nodes = children(h61);
			t12 = claim_text(h61_nodes, "2. ");
			t13 = claim_text(h61_nodes, t13_value);
			h61_nodes.forEach(detach);
			t14 = claim_space(section1_nodes);
			ul1 = claim_element(section1_nodes, "UL", {});
			var ul1_nodes = children(ul1);
			li3 = claim_element(ul1_nodes, "LI", { class: true });
			var li3_nodes = children(li3);
			t15 = claim_text(li3_nodes, "a. ");
			t16 = claim_text(li3_nodes, t16_value);
			li3_nodes.forEach(detach);
			t17 = claim_space(ul1_nodes);
			li4 = claim_element(ul1_nodes, "LI", { class: true });
			var li4_nodes = children(li4);
			t18 = claim_text(li4_nodes, "b. ");
			t19 = claim_text(li4_nodes, t19_value);
			li4_nodes.forEach(detach);
			t20 = claim_space(ul1_nodes);
			li5 = claim_element(ul1_nodes, "LI", { class: true });
			var li5_nodes = children(li5);
			t21 = claim_text(li5_nodes, "c. ");
			t22 = claim_text(li5_nodes, t22_value);
			li5_nodes.forEach(detach);
			t23 = claim_space(ul1_nodes);
			li6 = claim_element(ul1_nodes, "LI", { class: true });
			var li6_nodes = children(li6);
			t24 = claim_text(li6_nodes, "d. ");
			t25 = claim_text(li6_nodes, t25_value);
			li6_nodes.forEach(detach);
			ul1_nodes.forEach(detach);
			section1_nodes.forEach(detach);
			t26 = claim_space(ol_nodes);
			section2 = claim_element(ol_nodes, "SECTION", { id: true });
			var section2_nodes = children(section2);
			h62 = claim_element(section2_nodes, "H6", { class: true });
			var h62_nodes = children(h62);
			t27 = claim_text(h62_nodes, "3. ");
			t28 = claim_text(h62_nodes, t28_value);
			h62_nodes.forEach(detach);
			t29 = claim_space(section2_nodes);
			ul2 = claim_element(section2_nodes, "UL", {});
			var ul2_nodes = children(ul2);
			li7 = claim_element(ul2_nodes, "LI", { class: true });
			var li7_nodes = children(li7);
			t30 = claim_text(li7_nodes, "a. ");
			t31 = claim_text(li7_nodes, t31_value);
			li7_nodes.forEach(detach);
			t32 = claim_space(ul2_nodes);
			li8 = claim_element(ul2_nodes, "LI", { class: true });
			var li8_nodes = children(li8);
			t33 = claim_text(li8_nodes, "b. ");
			t34 = claim_text(li8_nodes, t34_value);
			li8_nodes.forEach(detach);
			ul2_nodes.forEach(detach);
			section2_nodes.forEach(detach);
			t35 = claim_space(ol_nodes);
			section3 = claim_element(ol_nodes, "SECTION", { id: true });
			var section3_nodes = children(section3);
			h63 = claim_element(section3_nodes, "H6", { class: true });
			var h63_nodes = children(h63);
			t36 = claim_text(h63_nodes, "4. ");
			t37 = claim_text(h63_nodes, t37_value);
			h63_nodes.forEach(detach);
			t38 = claim_space(section3_nodes);
			ul3 = claim_element(section3_nodes, "UL", {});
			var ul3_nodes = children(ul3);
			li9 = claim_element(ul3_nodes, "LI", { class: true });
			var li9_nodes = children(li9);
			t39 = claim_text(li9_nodes, "a. ");
			t40 = claim_text(li9_nodes, t40_value);
			li9_nodes.forEach(detach);
			t41 = claim_space(ul3_nodes);
			li10 = claim_element(ul3_nodes, "LI", { class: true });
			var li10_nodes = children(li10);
			t42 = claim_text(li10_nodes, "b. ");
			t43 = claim_text(li10_nodes, t43_value);
			li10_nodes.forEach(detach);
			ul3_nodes.forEach(detach);
			section3_nodes.forEach(detach);
			t44 = claim_space(ol_nodes);
			section4 = claim_element(ol_nodes, "SECTION", { id: true });
			var section4_nodes = children(section4);
			h64 = claim_element(section4_nodes, "H6", { class: true });
			var h64_nodes = children(h64);
			t45 = claim_text(h64_nodes, "5. ");
			t46 = claim_text(h64_nodes, t46_value);
			h64_nodes.forEach(detach);
			t47 = claim_space(section4_nodes);
			ul4 = claim_element(section4_nodes, "UL", {});
			var ul4_nodes = children(ul4);
			li11 = claim_element(ul4_nodes, "LI", { class: true });
			var li11_nodes = children(li11);
			t48 = claim_text(li11_nodes, "a. ");
			t49 = claim_text(li11_nodes, t49_value);
			li11_nodes.forEach(detach);
			t50 = claim_space(ul4_nodes);
			li12 = claim_element(ul4_nodes, "LI", { class: true });
			var li12_nodes = children(li12);
			t51 = claim_text(li12_nodes, "b. ");
			t52 = claim_text(li12_nodes, t52_value);
			li12_nodes.forEach(detach);
			ul4_nodes.forEach(detach);
			section4_nodes.forEach(detach);
			t53 = claim_space(ol_nodes);
			section5 = claim_element(ol_nodes, "SECTION", { id: true });
			var section5_nodes = children(section5);
			h65 = claim_element(section5_nodes, "H6", { class: true });
			var h65_nodes = children(h65);
			t54 = claim_text(h65_nodes, "6. ");
			t55 = claim_text(h65_nodes, t55_value);
			h65_nodes.forEach(detach);
			t56 = claim_space(section5_nodes);
			ul5 = claim_element(section5_nodes, "UL", {});
			var ul5_nodes = children(ul5);
			li13 = claim_element(ul5_nodes, "LI", { class: true });
			var li13_nodes = children(li13);
			t57 = claim_text(li13_nodes, "a. ");
			t58 = claim_text(li13_nodes, t58_value);
			li13_nodes.forEach(detach);
			ul5_nodes.forEach(detach);
			section5_nodes.forEach(detach);
			t59 = claim_space(ol_nodes);
			section6 = claim_element(ol_nodes, "SECTION", { id: true });
			var section6_nodes = children(section6);
			h66 = claim_element(section6_nodes, "H6", { class: true });
			var h66_nodes = children(h66);
			t60 = claim_text(h66_nodes, "7. ");
			t61 = claim_text(h66_nodes, t61_value);
			h66_nodes.forEach(detach);
			t62 = claim_space(section6_nodes);
			ul6 = claim_element(section6_nodes, "UL", {});
			var ul6_nodes = children(ul6);
			li14 = claim_element(ul6_nodes, "LI", { class: true });
			var li14_nodes = children(li14);
			t63 = claim_text(li14_nodes, "a. ");
			t64 = claim_text(li14_nodes, t64_value);
			li14_nodes.forEach(detach);
			ul6_nodes.forEach(detach);
			section6_nodes.forEach(detach);
			ol_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h60, "class", "h700");
			attr(li0, "class", "p-medium");
			attr(li1, "class", "p-medium");
			attr(li2, "class", "p-medium");
			attr(section0, "id", "1");
			attr(h61, "class", "h700");
			attr(li3, "class", "p-medium");
			attr(li4, "class", "p-medium");
			attr(li5, "class", "p-medium");
			attr(li6, "class", "p-medium");
			attr(section1, "id", "2");
			attr(h62, "class", "h700");
			attr(li7, "class", "p-medium");
			attr(li8, "class", "p-medium");
			attr(section2, "id", "3");
			attr(h63, "class", "h700");
			attr(li9, "class", "p-medium");
			attr(li10, "class", "p-medium");
			attr(section3, "id", "4");
			attr(h64, "class", "h700");
			attr(li11, "class", "p-medium");
			attr(li12, "class", "p-medium");
			attr(section4, "id", "5");
			attr(h65, "class", "h700");
			attr(li13, "class", "p-medium");
			attr(section5, "id", "6");
			attr(h66, "class", "h700");
			attr(li14, "class", "p-medium");
			attr(section6, "id", "7");
			attr(div0, "class", "wrapper svelte-6db1kc");
			attr(div1, "class", "section");
			attr(div1, "id", "section-0cd99f3a");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, ol);
			append_hydration(ol, section0);
			append_hydration(section0, h60);
			append_hydration(h60, t0);
			append_hydration(h60, t1);
			append_hydration(section0, t2);
			append_hydration(section0, ul0);
			append_hydration(ul0, li0);
			append_hydration(li0, t3);
			append_hydration(li0, t4);
			append_hydration(ul0, t5);
			append_hydration(ul0, li1);
			append_hydration(li1, t6);
			append_hydration(li1, t7);
			append_hydration(ul0, t8);
			append_hydration(ul0, li2);
			append_hydration(li2, t9);
			append_hydration(li2, t10);
			append_hydration(ol, t11);
			append_hydration(ol, section1);
			append_hydration(section1, h61);
			append_hydration(h61, t12);
			append_hydration(h61, t13);
			append_hydration(section1, t14);
			append_hydration(section1, ul1);
			append_hydration(ul1, li3);
			append_hydration(li3, t15);
			append_hydration(li3, t16);
			append_hydration(ul1, t17);
			append_hydration(ul1, li4);
			append_hydration(li4, t18);
			append_hydration(li4, t19);
			append_hydration(ul1, t20);
			append_hydration(ul1, li5);
			append_hydration(li5, t21);
			append_hydration(li5, t22);
			append_hydration(ul1, t23);
			append_hydration(ul1, li6);
			append_hydration(li6, t24);
			append_hydration(li6, t25);
			append_hydration(ol, t26);
			append_hydration(ol, section2);
			append_hydration(section2, h62);
			append_hydration(h62, t27);
			append_hydration(h62, t28);
			append_hydration(section2, t29);
			append_hydration(section2, ul2);
			append_hydration(ul2, li7);
			append_hydration(li7, t30);
			append_hydration(li7, t31);
			append_hydration(ul2, t32);
			append_hydration(ul2, li8);
			append_hydration(li8, t33);
			append_hydration(li8, t34);
			append_hydration(ol, t35);
			append_hydration(ol, section3);
			append_hydration(section3, h63);
			append_hydration(h63, t36);
			append_hydration(h63, t37);
			append_hydration(section3, t38);
			append_hydration(section3, ul3);
			append_hydration(ul3, li9);
			append_hydration(li9, t39);
			append_hydration(li9, t40);
			append_hydration(ul3, t41);
			append_hydration(ul3, li10);
			append_hydration(li10, t42);
			append_hydration(li10, t43);
			append_hydration(ol, t44);
			append_hydration(ol, section4);
			append_hydration(section4, h64);
			append_hydration(h64, t45);
			append_hydration(h64, t46);
			append_hydration(section4, t47);
			append_hydration(section4, ul4);
			append_hydration(ul4, li11);
			append_hydration(li11, t48);
			append_hydration(li11, t49);
			append_hydration(ul4, t50);
			append_hydration(ul4, li12);
			append_hydration(li12, t51);
			append_hydration(li12, t52);
			append_hydration(ol, t53);
			append_hydration(ol, section5);
			append_hydration(section5, h65);
			append_hydration(h65, t54);
			append_hydration(h65, t55);
			append_hydration(section5, t56);
			append_hydration(section5, ul5);
			append_hydration(ul5, li13);
			append_hydration(li13, t57);
			append_hydration(li13, t58);
			append_hydration(ol, t59);
			append_hydration(ol, section6);
			append_hydration(section6, h66);
			append_hydration(h66, t60);
			append_hydration(h66, t61);
			append_hydration(section6, t62);
			append_hydration(section6, ul6);
			append_hydration(ul6, li14);
			append_hydration(li14, t63);
			append_hydration(li14, t64);
		},
		p(ctx, [dirty]) {
			if (dirty & /*bullet_1*/ 1 && t1_value !== (t1_value = /*bullet_1*/ ctx[0].title + "")) set_data(t1, t1_value);
			if (dirty & /*bullet_1*/ 1 && t4_value !== (t4_value = /*bullet_1*/ ctx[0].a + "")) set_data(t4, t4_value);
			if (dirty & /*bullet_1*/ 1 && t7_value !== (t7_value = /*bullet_1*/ ctx[0].b + "")) set_data(t7, t7_value);
			if (dirty & /*bullet_1*/ 1 && t10_value !== (t10_value = /*bullet_1*/ ctx[0].c + "")) set_data(t10, t10_value);
			if (dirty & /*bullet_2*/ 2 && t13_value !== (t13_value = /*bullet_2*/ ctx[1].title + "")) set_data(t13, t13_value);
			if (dirty & /*bullet_2*/ 2 && t16_value !== (t16_value = /*bullet_2*/ ctx[1].a + "")) set_data(t16, t16_value);
			if (dirty & /*bullet_2*/ 2 && t19_value !== (t19_value = /*bullet_2*/ ctx[1].b + "")) set_data(t19, t19_value);
			if (dirty & /*bullet_2*/ 2 && t22_value !== (t22_value = /*bullet_2*/ ctx[1].c + "")) set_data(t22, t22_value);
			if (dirty & /*bullet_2*/ 2 && t25_value !== (t25_value = /*bullet_2*/ ctx[1].d + "")) set_data(t25, t25_value);
			if (dirty & /*bullet_3*/ 4 && t28_value !== (t28_value = /*bullet_3*/ ctx[2].title + "")) set_data(t28, t28_value);
			if (dirty & /*bullet_3*/ 4 && t31_value !== (t31_value = /*bullet_3*/ ctx[2].a + "")) set_data(t31, t31_value);
			if (dirty & /*bullet_3*/ 4 && t34_value !== (t34_value = /*bullet_3*/ ctx[2].b + "")) set_data(t34, t34_value);
			if (dirty & /*bullet_4*/ 8 && t37_value !== (t37_value = /*bullet_4*/ ctx[3].title + "")) set_data(t37, t37_value);
			if (dirty & /*bullet_4*/ 8 && t40_value !== (t40_value = /*bullet_4*/ ctx[3].a + "")) set_data(t40, t40_value);
			if (dirty & /*bullet_4*/ 8 && t43_value !== (t43_value = /*bullet_4*/ ctx[3].b + "")) set_data(t43, t43_value);
			if (dirty & /*bullet_5*/ 16 && t46_value !== (t46_value = /*bullet_5*/ ctx[4].title + "")) set_data(t46, t46_value);
			if (dirty & /*bullet_5*/ 16 && t49_value !== (t49_value = /*bullet_5*/ ctx[4].a + "")) set_data(t49, t49_value);
			if (dirty & /*bullet_5*/ 16 && t52_value !== (t52_value = /*bullet_5*/ ctx[4].b + "")) set_data(t52, t52_value);
			if (dirty & /*bullet_6*/ 32 && t55_value !== (t55_value = /*bullet_6*/ ctx[5].title + "")) set_data(t55, t55_value);
			if (dirty & /*bullet_6*/ 32 && t58_value !== (t58_value = /*bullet_6*/ ctx[5].a + "")) set_data(t58, t58_value);
			if (dirty & /*bullet_7*/ 64 && t61_value !== (t61_value = /*bullet_7*/ ctx[6].title + "")) set_data(t61, t61_value);
			if (dirty & /*bullet_7*/ 64 && t64_value !== (t64_value = /*bullet_7*/ ctx[6].a + "")) set_data(t64, t64_value);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { bullet_1 } = $$props;
	let { bullet_2 } = $$props;
	let { bullet_3 } = $$props;
	let { bullet_4 } = $$props;
	let { bullet_5 } = $$props;
	let { bullet_6 } = $$props;
	let { bullet_7 } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(7, favicon = $$props.favicon);
		if ('bullet_1' in $$props) $$invalidate(0, bullet_1 = $$props.bullet_1);
		if ('bullet_2' in $$props) $$invalidate(1, bullet_2 = $$props.bullet_2);
		if ('bullet_3' in $$props) $$invalidate(2, bullet_3 = $$props.bullet_3);
		if ('bullet_4' in $$props) $$invalidate(3, bullet_4 = $$props.bullet_4);
		if ('bullet_5' in $$props) $$invalidate(4, bullet_5 = $$props.bullet_5);
		if ('bullet_6' in $$props) $$invalidate(5, bullet_6 = $$props.bullet_6);
		if ('bullet_7' in $$props) $$invalidate(6, bullet_7 = $$props.bullet_7);
	};

	return [bullet_1, bullet_2, bullet_3, bullet_4, bullet_5, bullet_6, bullet_7, favicon];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			favicon: 7,
			bullet_1: 0,
			bullet_2: 1,
			bullet_3: 2,
			bullet_4: 3,
			bullet_5: 4,
			bullet_6: 5,
			bullet_7: 6
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$5(ctx) {
	let div1;
	let div0;
	let h6;
	let t0;
	let t1;
	let p0;
	let t2;
	let t3;
	let p1;
	let strong;
	let t4;
	let a;
	let t5;
	let a_href_value;
	let t6;
	let p2;
	let t7;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			h6 = element("h6");
			t0 = text(/*content_title*/ ctx[0]);
			t1 = space();
			p0 = element("p");
			t2 = text(/*content_description*/ ctx[1]);
			t3 = space();
			p1 = element("p");
			strong = element("strong");
			t4 = text("Email:");
			a = element("a");
			t5 = text(/*email*/ ctx[2]);
			t6 = space();
			p2 = element("p");
			t7 = text(/*last_updated*/ ctx[3]);
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h6 = claim_element(div0_nodes, "H6", { class: true });
			var h6_nodes = children(h6);
			t0 = claim_text(h6_nodes, /*content_title*/ ctx[0]);
			h6_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			p0 = claim_element(div0_nodes, "P", { class: true });
			var p0_nodes = children(p0);
			t2 = claim_text(p0_nodes, /*content_description*/ ctx[1]);
			p0_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			p1 = claim_element(div0_nodes, "P", { class: true });
			var p1_nodes = children(p1);
			strong = claim_element(p1_nodes, "STRONG", {});
			var strong_nodes = children(strong);
			t4 = claim_text(strong_nodes, "Email:");
			strong_nodes.forEach(detach);
			a = claim_element(p1_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t5 = claim_text(a_nodes, /*email*/ ctx[2]);
			a_nodes.forEach(detach);
			p1_nodes.forEach(detach);
			t6 = claim_space(div0_nodes);
			p2 = claim_element(div0_nodes, "P", { class: true });
			var p2_nodes = children(p2);
			t7 = claim_text(p2_nodes, /*last_updated*/ ctx[3]);
			p2_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h6, "class", "h700");
			attr(p0, "class", "p-medium");
			attr(a, "class", "link svelte-gyev31");
			attr(a, "href", a_href_value = `mailto:${/*email*/ ctx[2]}`);
			attr(p1, "class", "p-medium");
			attr(p2, "class", "p-medium");
			attr(div0, "class", "wrapper svelte-gyev31");
			attr(div1, "class", "section");
			attr(div1, "id", "section-05d7debc");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, h6);
			append_hydration(h6, t0);
			append_hydration(div0, t1);
			append_hydration(div0, p0);
			append_hydration(p0, t2);
			append_hydration(div0, t3);
			append_hydration(div0, p1);
			append_hydration(p1, strong);
			append_hydration(strong, t4);
			append_hydration(p1, a);
			append_hydration(a, t5);
			append_hydration(div0, t6);
			append_hydration(div0, p2);
			append_hydration(p2, t7);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title*/ 1) set_data(t0, /*content_title*/ ctx[0]);
			if (dirty & /*content_description*/ 2) set_data(t2, /*content_description*/ ctx[1]);
			if (dirty & /*email*/ 4) set_data(t5, /*email*/ ctx[2]);

			if (dirty & /*email*/ 4 && a_href_value !== (a_href_value = `mailto:${/*email*/ ctx[2]}`)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*last_updated*/ 8) set_data(t7, /*last_updated*/ ctx[3]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_description } = $$props;
	let { email } = $$props;
	let { last_updated } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_description' in $$props) $$invalidate(1, content_description = $$props.content_description);
		if ('email' in $$props) $$invalidate(2, email = $$props.email);
		if ('last_updated' in $$props) $$invalidate(3, last_updated = $$props.last_updated);
	};

	return [content_title, content_description, email, last_updated, favicon];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			favicon: 4,
			content_title: 0,
			content_description: 1,
			email: 2,
			last_updated: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	return child_ctx;
}

// (70:4) {#each nav as { link }}
function create_each_block$1(ctx) {
	let h6;
	let a;
	let t0_value = /*link*/ ctx[3].label + "";
	let t0;
	let a_target_value;
	let a_href_value;
	let t1;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { id: true, class: true });
			var h6_nodes = children(h6);
			a = claim_element(h6_nodes, "A", { target: true, class: true, href: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(h6_nodes);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "target", a_target_value = /*link*/ ctx[3].label.includes('Whitepaper')
			? '_blank'
			: '_self');

			attr(a, "class", "link svelte-14fdjq7");
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(h6, "id", "links");
			attr(h6, "class", "h950 svelte-14fdjq7");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t0);
			append_hydration(h6, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 1 && t0_value !== (t0_value = /*link*/ ctx[3].label + "")) set_data(t0, t0_value);

			if (dirty & /*nav*/ 1 && a_target_value !== (a_target_value = /*link*/ ctx[3].label.includes('Whitepaper')
			? '_blank'
			: '_self')) {
				attr(a, "target", a_target_value);
			}

			if (dirty & /*nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

function create_fragment$6(ctx) {
	let div;
	let footer;
	let nav_1;
	let t0;
	let span;
	let p;
	let t1;
	let each_value = /*nav*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div = element("div");
			footer = element("footer");
			nav_1 = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			span = element("span");
			p = element("p");
			t1 = text(/*copyright*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			footer = claim_element(div_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			nav_1 = claim_element(footer_nodes, "NAV", { class: true });
			var nav_1_nodes = children(nav_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_1_nodes);
			}

			nav_1_nodes.forEach(detach);
			t0 = claim_space(footer_nodes);
			span = claim_element(footer_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			p = claim_element(span_nodes, "P", { id: true, class: true });
			var p_nodes = children(p);
			t1 = claim_text(p_nodes, /*copyright*/ ctx[1]);
			p_nodes.forEach(detach);
			span_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav_1, "class", "svelte-14fdjq7");
			attr(p, "id", "copyright");
			attr(p, "class", "p-small svelte-14fdjq7");
			attr(span, "class", "svelte-14fdjq7");
			attr(footer, "class", "section-container svelte-14fdjq7");
			attr(div, "class", "section");
			attr(div, "id", "section-dabd6025");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, footer);
			append_hydration(footer, nav_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav_1, null);
				}
			}

			append_hydration(footer, t0);
			append_hydration(footer, span);
			append_hydration(span, p);
			append_hydration(p, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*nav*/ 1) {
				each_value = /*nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav_1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*copyright*/ 2) set_data(t1, /*copyright*/ ctx[1]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { nav } = $$props;
	let { copyright } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('nav' in $$props) $$invalidate(0, nav = $$props.nav);
		if ('copyright' in $$props) $$invalidate(1, copyright = $$props.copyright);
	};

	return [nav, copyright, favicon];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$6, create_fragment$6, safe_not_equal, { favicon: 2, nav: 0, copyright: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function instance$7($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$7, null, safe_not_equal, { favicon: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$7(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let current;

	component_0 = new Component({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				}
			}
		});

	component_1 = new Component$2({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				logo: {
					"image": {
						"alt": "logo",
						"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778unlok-logo2%20copy.svg",
						"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778unlok-logo2%20copy.svg",
						"size": 3
					},
					"title": ""
				},
				site_nav: [
					{
						"link": { "url": "/personal", "label": "Personal" }
					},
					{
						"link": {
							"url": "/business",
							"label": "Business",
							"active": false
						}
					},
					{
						"link": { "url": "/investor", "label": "Investor" }
					}
				],
				site_nav_button: { "url": "/portal", "label": "Get Started" }
			}
		});

	component_2 = new Component$3({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				logo: {
					"image": {
						"alt": "logo",
						"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778Subtract.svg",
						"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778Subtract.svg",
						"size": 1
					},
					"title": ""
				},
				site_nav: [
					{
						"link": { "url": "/personal", "label": "Personal" }
					},
					{
						"link": {
							"url": "/business",
							"label": "Business",
							"active": false
						}
					},
					{
						"link": { "url": "/team", "label": "Investor" }
					}
				],
				site_nav_button: "Get Started",
				hero_title_1: "Privacy Policy",
				hero_title_2: "Effective Date: May 1, 2023",
				hero_description: "At UNLOK, we are committed to protecting your privacy and safeguarding the personal information of our users and business partners. This Privacy Policy outlines how we collect, use, disclose, and protect your data when you interact with our blockchain rewards platform and related services. We encourage you to read this policy carefully to understand our practices regarding your personal information."
			}
		});

	component_3 = new Component$4({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				bullet_1: {
					"a": "Personal Information from Users: When you create an account with UNLOK, we may collect personal information such as your name, email address, contact details, and other relevant information you provide to us during the registration process. To enhance your user experience and improve our services, we may collect information related to your transactions, rewards earned, preferences, and interactions with our platform.",
					"b": "Personal Information from Businesses: If you are a business partner or service provider, we may collect personal information such as your name, email address, company details, and other necessary information to establish and maintain a business relationship.",
					"c": "Usage Information: When you access our platform, we automatically collect certain information about your usage patterns, browsing activities, IP address, device information, and other similar data. This information is used to analyze and improve the performance and functionality of our platform.",
					"itle": "",
					"title": "Information We Collect"
				},
				bullet_2: {
					"a": "Providing and Improving Services: We use the information we collect to provide, maintain, and improve our blockchain rewards platform and related services. Your personal information helps us personalize your experience, facilitate transactions, communicate with you, and address any inquiries or support requests.",
					"b": "Rewards and Loyalty Programs: The data we collect enables us to effectively administer rewards and loyalty programs, allowing users to earn, redeem, and manage their rewards within our platform.",
					"c": "Communication: We may use your personal information to communicate with you and provide updates, promotional offers, and other relevant information about our services. You can choose to opt out of receiving promotional communications at any time.",
					"d": "Business Relationships: If you are a business partner or service provider, we may use your personal information to establish, manage, and maintain our business relationship, including fulfilling contractual obligations, processing payments, and providing customer support.",
					"title": "Use of Information"
				},
				bullet_3: {
					"a": "Third-Party Service Providers: We may engage trusted third-party service providers to assist us in delivering our services, such as payment processors, analytics providers, and customer support services. These providers are bound by strict confidentiality obligations and are only authorized to use your personal information as necessary to perform the requested services.",
					"b": "Compliance with Legal Obligations: We may disclose your personal information if required by law, regulation, or legal process or in response to a valid request from law enforcement authorities, government agencies, or regulatory bodies.",
					"title": "Data Sharing and Disclosure"
				},
				bullet_4: {
					"a": "Data Protection Measures: We employ industry-standard security measures to protect your personal information from unauthorized access, disclosure, alteration, or destruction. These measures include encryption, access controls, firewalls, and regular security assessments.",
					"b": "User Responsibilities: While we strive to protect your personal information, it is essential for users to maintain the security and confidentiality of their account credentials and exercise caution when sharing personal information online.",
					"title": "Data Security"
				},
				bullet_5: {
					"a": "Access, Update, and Deletion: You have the right to access, update, correct, or delete your personal information held by us. You can manage your account settings and preferences within our platform or contact us using the information provided below.",
					"b": "Marketing Communications: You have the option to opt out of receiving marketing communications from us. You can exercise this choice by following the unsubscribe instructions in our communications or contacting us directly.",
					"title": "Your Rights and Choices"
				},
				bullet_6: {
					"a": "Third-Party Websites and Services: Our platform may contain links to third-party websites or services that are not operated or controlled by us. This Privacy Policy does not apply to those third-party websites, and we encourage you to review the privacy policies of such websites before providing any personal information.",
					"title": "Links to Third-Party Websites"
				},
				bullet_7: {
					"a": "Policy Updates:  We reserve the right to update or modify this Privacy Policy anytime. Any changes will be effective upon posting the revised policy on our platform. We encourage you to review this policy periodically to stay informed about our privacy practices.",
					"title": "Changes to this Privacy Policy"
				}
			}
		});

	component_4 = new Component$5({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title: "Contact Us",
				content_description: "If you have any questions, concerns, or requests regarding this Privacy Policy or the handling of your personal information, please contact us at:",
				email: "info@unlokloyalty.com",
				last_updated: "Last updated: May 24, 2023"
			}
		});

	component_5 = new Component$6({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				nav: [
					{
						"link": {
							"url": "/tokenomics",
							"label": "Tokenomics"
						}
					},
					{
						"link": {
							"url": "/privacy",
							"label": "Privacy Policy"
						}
					},
					{
						"link": {
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/Whitepaper.pdf?t=2023-06-23T23%3A35%3A42.985Z",
							"label": "Whitepaper"
						}
					},
					{
						"link": {
							"url": "https://unlokloyalty.com#contact-us",
							"label": "Contact Us"
						}
					}
				],
				copyright: "© 2023 UNLOK. All rights reserved."
			}
		});

	component_6 = new Component$7({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				}
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
		}
	};
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$7, safe_not_equal, {});
	}
}

export default Component$8;
