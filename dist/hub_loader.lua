-- ===== Key System =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


-- Y2k key background. Paste your uploaded Roblox image id (e.g. "rbxassetid://123456")
-- to show it behind the key box. Leave "" for the blue-chrome gradient. For the
-- blurred look, upload a pre-blurred version of the image to Roblox and use its id.
local KEY_BG_IMAGE = ""

local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Y2k chrome backdrop (full-screen, behind everything)
	local backdrop = Instance.new("ImageLabel")
	backdrop.Name = "Y2kBackdrop"
	backdrop.Size = UDim2.fromScale(1, 1)
	backdrop.BackgroundColor3 = Color3.fromRGB(4, 4, 12)
	backdrop.BorderSizePixel = 0
	backdrop.Image = KEY_BG_IMAGE or ""
	backdrop.ScaleType = Enum.ScaleType.Crop
	backdrop.ImageTransparency = 0.12
	backdrop.ZIndex = -10
	backdrop.Parent = screen
	-- blue-chrome gradient (shows through when no image / tints the image)
	local bgGrad = Instance.new("UIGradient")
	bgGrad.Color = ColorSequence.new({
		ColorSequenceKeypoint.new(0, Color3.fromRGB(58, 40, 150)),
		ColorSequenceKeypoint.new(0.5, Color3.fromRGB(24, 28, 70)),
		ColorSequenceKeypoint.new(1, Color3.fromRGB(8, 10, 28)),
	})
	bgGrad.Rotation = 45
	bgGrad.Parent = backdrop
	backdrop.BackgroundTransparency = (KEY_BG_IMAGE ~= "" and 0.25) or 0
	-- soft fade so the key card pops
	local vignette = Instance.new("Frame")
	vignette.Size = UDim2.fromScale(1, 1)
	vignette.BackgroundColor3 = Color3.fromRGB(2, 2, 8)
	vignette.BackgroundTransparency = 0.35
	vignette.BorderSizePixel = 0
	vignette.ZIndex = -9
	vignette.Parent = screen

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = (box.Text:gsub("%s+", "")) -- trim spaces; keep case (work.ink tokens are lowercase)
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
do
  local MAP = {
    [95082159892680] = 'Keyboard escape/keyboard escape',
    [118941584817777] = 'Keyboard escape/keyboard escape',
    [92416421522960] = 'Slime rng/SlimeRNG_Script',
    [79268393072444] = 'Sell a Lemon/Sell a Lemon',
    [89469502395769] = 'Kick a Lucky Block/Kick a Lucky Block',
    [17625359962] = 'RIVALS/Rivals',
    [126884695634066] = 'Grow A garden/Grow-a-garden',
    [131048399685555] = 'Strongest Battleground/TSB',
    [16732694052] = 'FIsch It/Pechez-le',
    [16116270224] = 'Dandy World/Dandy-World',
    [73956553001240] = 'VolleyBall Legend/VolleyBall-Legends',
  }
  local name = MAP[game.PlaceId]
  if not name then return warn('[Y2k] this game is not supported yet (PlaceId ' .. tostring(game.PlaceId) .. ')') end
  local KEY = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key
  local HWID = getgenv and getgenv().HWID
  if not HWID or HWID == '' then
    pcall(function() HWID = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
    if not HWID then pcall(function() HWID = game:GetService('RbxAnalyticsService'):GetClientId() end) end
  end
  HWID = tostring(HWID or 'unknown')
  local HS = game:GetService('HttpService')
  local function enc(s) local ok,r = pcall(function() return HS:UrlEncode(s) end) return ok and r or s end
  local function httpGet(u)
    for _,f in ipairs({
      function() return game:HttpGetAsync(u) end,
      function() return game:HttpGet(u) end,
      function() return request and request({Url=u,Method='GET'}).Body end,
    }) do local ok,b = pcall(f) if ok and type(b)=='string' then return b end end
  end
  local url = 'https://y2k-keys.y2kscript.workers.dev' .. '/deliver?name=' .. enc(name) .. '&key=' .. enc(tostring(KEY)) .. '&hwid=' .. enc(HWID)
  local body = httpGet(url)
  if not body then return warn('[Y2k] server unreachable') end
  if string.sub(body,1,3) ~= 'ok\n' then return warn('[Y2k] ' .. tostring(body)) end
  local fn = (loadstring or load)(string.sub(body,4), '=Y2k')
  if fn then fn() else warn('[Y2k] load failed') end
end
